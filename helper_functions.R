require(logitnorm)
require(magrittr)
require(flux)

biasedLogit <- function(p, a) {
  # An implementation of the biased logit function (Satopaa et al. 2014).
  log((p / (1 - p)) ^ (1 / a))
}

randomOdds <- function(p, a = 1, mu = 0, sigma, n) {
  # Generates odds from linear combinations of the logit of an
  # underlying probability that an event would have occured if the
  # scenario ultimately occurs.
  logOdds <- biasedLogit(p, a) + rnorm(n, mean = mu, sd = sigma)
  P <- invlogit(logOdds)
  P / (1 - P)
}

infoAssymetry <- function(p, a = 1, mu = 0,
                          sigma, p_c, n = 30, m = 1000,
                          sampleProb = TRUE, Brier = TRUE) {
  
  # Generate "true" event likelihood ratios from the model
  eventOdds <- lapply(1:m,
                      function(x) randomOdds(p, a, mu = mu, sigma = sigma, n = n))
  
  # Multiply events to determine the odds of the scenario occuring
  trueWalk <- lapply(eventOdds, cumprod)
  
  # Flip the - biased - coin and determine if the event actually occured
  trueResults <- sapply(trueWalk, function(x) runif(1) <= x[n])
  
  # There are two forms of sampling.  One (if sampleProb is TRUE) uses probabilistic
  # sampling.  The other uses fixed length random samples without replacement.
  if(sampleProb) {
    eventSample <- lapply(eventOdds, function(x) c(x[sort(which(runif(n) <= p_c))]))
  } else {
    eventSample <- lapply(eventOdds, function(x) c(sample(x, p_c)))
  }
  
  # Evolve the sampled likelihood ratios to forecast the scenario odds
  eventWalk <- lapply(eventSample, cumprod)
  
  # Convert odds to probabilities
  forecastScenario <- lapply(eventWalk, function(x) x / (1 + x))
  
  # Compute the final probabilities
  forecastFinal <- sapply(forecastScenario, function(x) x[length(x)])
  
  # Compute Brier scores if requested
  if(Brier) return ((trueResults - forecastFinal) ^ 2)
  
  # Compute confusion matricies if Brier scores are not requested
  forecastBinary <- forecastFinal > 0.5
  truePos <- sum(forecastBinary + trueResults == 2)
  trueNeg <- sum(forecastBinary + trueResults == 0)
  falsePos <- sum(forecastBinary == TRUE) - truePos
  falseNeg <- length(forecastBinary) - truePos - trueNeg - falsePos
  return(list(truePos = truePos,
              trueNeg = trueNeg,
              falsePos = falsePos,
              falseNeg = falseNeg))
}

construct_confusion_matricies <- function(confusionList, m = 1000) {
  # Takes the output of infoAssymetry with Brier = False and collapses the nested lists
  # into a list of four vectors, one each for true positives, true negatives,
  # false positives, and false negatives.  These values are normalized by the number
  # of simulations.
  
  baseList <- list(truePos = sapply(confusionList, function(x) x$truePos / m),
                   trueNeg = sapply(confusionList, function(x) x$trueNeg / m),
                   falsePos = sapply(confusionList, function(x) x$falsePos / m),
                   falseNeg = sapply(confusionList, function(x) x$falseNeg / m))
  
  return(as.data.frame(baseList))
}

IEM_to_residuals <- function(IEM_file) {
  IEM <- read.csv(IEM_file, stringsAsFactors = FALSE)
  IEM$Date <- as.Date(IEM$Date, '%m/%d/%y')
  IEM_split <- split(IEM, IEM$Contract)
  prob_1 <- IEM_split[[1]]$LastPrice
  odds_1 <- prob_1 / (1 - prob_1)
  length_odds <- length(odds_1)
  likelihood_1 <- odds_1[2:length_odds] / odds_1[1:(length_odds - 1)]
  marg_prob_1 <- likelihood_1 / (1 + likelihood_1)
  resid <- marg_prob_1 - mean(marg_prob_1)
  resid <- resid[1:(length(resid) - 5)]
  qqnorm(resid)
  qqline(resid)
  s_test <- shapiro.test(resid)
  list(Underlying_Mean = mean(marg_prob_1),
       Mean = mean(resid),
       SD = sd(resid),
       W = as.numeric(s_test[[1]]),
       p = s_test[[2]])
}

synthetic_data <- function(n, sigma) {
  # Generate synthetic probability evolutions used to
  # test forecasts of binary scenarios
  
  # Generate vector of Gaussian noise
  ε <- rnorm(n, sd = sigma)
  
  # Compute random walk of log-odds
  Y <- cumsum(ε)
  
  # Convert to probiablities
  P <- invlogit(Y)
  
  # And to odds
  O <- exp(Y)
  
  # And to likelihood ratios
  L <- exp(ε)
  
  # Build the output data frame
  returnList <- list(P = P, Y = Y, O = O, L = L, ε = ε)
  as.data.frame(returnList)
}

multiple_synthetic <- function(m, ...) {
  # Wrapper for vectorized call to the function synthetic_data
  
  lapply(1:m, function(x) synthetic_data(...))
}

p_to_epsilon <- function(P) {
  # Convert a vector of probabilities to a vector of marginal
  # information in log-odds space.
  
  # Convert the vector of probabilites to a vector of log-odds
  Y <- logit(P)
  
  # Take successive differences.  Remember that epsilon_1 = Y[1]
  c(Y[1], diff(Y))
}

learn_and_transfer <- function(dataDF, π = 0.5, sourceμ = 0, sourceσ = 0,
                               collectσ = 0, reportμ = 0, reportσ = 0, 
                               callFromExp2 = FALSE) {
  # Count the discrete items of evidence
  itemsEvidence <- nrow(dataDF)
  
  # Apply information assymetry
  learnedData <- which(runif(itemsEvidence) <= π)
  
  # Allow for the possiblity that no evidence is learned
  learnedLength <- length(learnedData)
  if(learnedLength == 0) {
    if(callFromExp2) {
      return(rep(0, itemsEvidence))
    }else{
      return(NULL)
    }
  }
  
  # Apply noise to learned data
  sourceRawData <- dataDF$ε[learnedData]
  sourceξ <- rnorm(learnedLength, sourceμ, sourceσ)
  sourceNoisyData <- sourceRawData + sourceξ
  
  # Conduct noisy transfer to collector
  collectξ <- rnorm(learnedLength, mean = 0, sd = collectσ)
  collectorData <- sourceNoisyData + collectξ
  
  # Conduct noisy reporting
  reportξ <- rnorm(learnedLength, reportμ, reportσ)
  reportedData <- collectorData + reportξ
  
  # Output the vector making explict the data loss to assymetry
  outputVector <- rep(0, itemsEvidence)
  outputVector[learnedData] <- reportedData
  return(outputVector)
}

generate_forecast <- function(learnXferOutput) {
  learnXferOutput %>%
    cumsum %>%
    invlogit
}

compute_measures_performance <- function(dataDF, forecast, Outcome = NA) {
  
  # Allow for the possiblity that no forecast was generated due
  # to no collection
  if(length(forecast) == 0) {
    return(list(Brier = NA, RMSE = NA, outcomeType = NA))
  }
  
  # Count the time steps
  timeSteps <- nrow(dataDF)
  
  # Determine if the event occured based on the final probability or the user's
  # input
  if(is.na(Outcome)) {
    eventOccured <- runif(1) <= dataDF$P[timeSteps]
  } else {
    eventOccured <- Outcome
  }
  
  # Compute the Brier score
  finalForecast <- forecast[timeSteps]
  Brier <- (as.numeric(eventOccured) - finalForecast) ^ 2 +
    (as.numeric(!eventOccured) - (1 - finalForecast)) ^ 2
  
  # Compute the squared error
  SE <- (dataDF$P[timeSteps] - forecast[timeSteps]) ^ 2
  
  # Classify the outcome under various thresholds
  outcomeType <- lapply(seq(0, 1, by = 0.05),
                        function(x) confusion_matrix(finalForecast,
                                                     eventOccured,
                                                     x))
  
  # Combine the output into a list
  list(Brier = Brier, SE = SE, outcomeType = outcomeType)
}

confusion_matrix <- function(finalForecast, eventOccured, threshold) {
  # Computes the confusion matrix for a given threshold
  
  # Determine the forecasted outcome based on the threshold
  eventPredict <- finalForecast > threshold
  
  # Classify the forecasts based on the forecsted outcomes and the
  # true outcomes
  if(eventOccured & eventPredict) outcomeType <- 'truePos'
  if(eventOccured & !eventPredict) outcomeType <- 'falseNeg'
  if(!eventOccured & eventPredict) outcomeType <- 'falsePos'
  if(!eventOccured & !eventPredict) outcomeType <- 'trueNeg'
  
  # Return the output vector
  return(outcomeType)
}

experiment_brier_assymetry_sigma <- function(m = 1000, n = 100,
                                             sigma = 0, sourceμ = 0,
                                             sourceσ = 0, collectσ = 0,
                                             reportμ = 0, reportσ = 0) {
  # Conducts a parameter sweep of values of π between 0.05 and 1 to 
  # examine the importance of aggressive informaton acquistion. By default
  # information transfer is noiseless, but these values can be adjusted to
  # explore the relative value of aggressive acquistion against noisy
  # regimes. Returns a vector of mean Brier scores associated with values
  # of π. Can be vectorized using lapply or mclapply; the latter requires
  # the parallel package.
  
  # Establish the vector of learning probabilities
  π <- seq(0.05, 1, by = 0.05)
  
  # Initialize the output vector
  outputBrier <- numeric(length(π))
  
  # Generate synthetic data
  experimentData <- multiple_synthetic(m = m, n = n, sigma = sigma)
  
  # Generate forecasts and measure the Brier score
  for(i in 1:length(π)) {
    dataLearn <- lapply(experimentData, function(x) learn_and_transfer(x, π[i],
                                                                       sourceμ, sourceσ,
                                                                       collectσ, reportμ,
                                                                       reportσ))
    dataForecast <- lapply(dataLearn, generate_forecast)
    dataMeasure <- lapply(1:m,
                          function(x) compute_measures_performance(experimentData[[x]],
                                                                   dataForecast[[x]]))
    Brier <- sapply(dataMeasure, function(x) x$Brier)
    outputBrier[i] <- mean(Brier, na.rm = TRUE)
  }
  
  outputBrier
}

learn_forecast_evaluate <- function(dataDF, ...) {
  # A wrapper function for the functions above. Takes as input a list
  # of data frames containing the synthetic data and inputs to the function
  # learn_and_transfer. Returns a list of five entries: Brier score for the
  # system, RMSE for the system, the system's ROC broken into the TPR and
  # FPR, and the area under the ROC curve.
  
  # Conduct vectorized learning and transfer of information from single source
  # to single collector.
  learnData <- lapply(dataDF, function(x) learn_and_transfer(x, ...))
  
  # Find and eliminate any instances in which no forecast was generated because
  # the source did not learn any evidence
  learnDataLength <- sapply(learnData, length)
  learnIndex <- which(learnDataLength != 0)
  learnData <- learnData[learnIndex]
  
  # Generate a forecast from each set of learned evidence
  forecastList <- lapply(learnData, generate_forecast)
  
  # Generate evaluate data for each forecast
  lengthData <- length(learnData)
  evalList <- lapply(1:lengthData,
                     function(x) compute_measures_performance(dataDF[[x]],
                                                              forecastList[[x]]))
  
  # Go through the resulting list, cull and compile the evaluation data into
  # vectors and matricies as needed for further reporting
  brierVec <- sapply(evalList, function(x) x$Brier)
  SEVec <- sapply(evalList, function(x) x$SE)
  
  # For the ROC curve, first collapse the ROC data into a matrix, then build a
  # list of four matricies for each of the possible outcomes, then take rowwise
  # sums through each matrix to compute the values needed for TPR and FPR.
  ROCMat <- sapply(evalList, function(x) x$outcomeType)
  ROCTypes <- lapply(c('truePos',
                       'trueNeg',
                       'falsePos',
                       'falseNeg'),
                     function(x) ROCMat == x)
  outcomeBreakout <- lapply(ROCTypes, function(x) apply(x, 1, sum))
  TPR <- outcomeBreakout[[1]] / (outcomeBreakout[[1]] + outcomeBreakout[[4]])
  FPR <- outcomeBreakout[[3]] / (outcomeBreakout[[3]] + outcomeBreakout[[2]])
  
  # Compute the area under the ROC curve using the auc function from the flux
  # package
  AUC <- auc(FPR, TPR)
  
  # Return a list
  list(Brier = mean(brierVec),
       RMSE = sqrt(mean(SEVec)),
       TPR = TPR,
       FPR = FPR,
       AUC = AUC)
}

parameter_sweep <- function(sourceσ) {
  
  # Discretize the computational domain
  sigma <- seq(0.1, 1, by = 0.1)
  Pi <- seq(0.1, 1, by = 0.1)
  
  # Initialize output matricies
  Output <- list(Brier = matrix(nrow = 10, ncol = 10),
                 RMSE = matrix(nrow = 10, ncol = 10),
                 AUC = matrix(nrow = 10, ncol = 10))
  
  # Loop through the domain
  for(i in 1:10) {
    for(j in 1:10) {
      
      # Generate 500 instances of synthetic data with 100 items of evidence each
      Data <- multiple_synthetic(500, 100, sigma = sigma[i])
      
      # Have the source learn the data and transfer it to the acquirer with
      # some noise but no bias applied. The acquirer passes the information to
      # the analysis layer without noise or bias.
      evalMeasures <- learn_forecast_evaluate(dataDF = Data, π = Pi[j],
                                               sourceμ = 0, sourceσ = sourceσ,
                                               collectσ = 0, reportμ = 0,
                                               reportσ = 0)
      
      # Collect the results in matricies
      Output$Brier[i,j] <- evalMeasures$Brier
      Output$RMSE[i,j] <- evalMeasures$RMSE
      Output$AUC[i,j] <- evalMeasures$AUC
    }
  }
  
  # Return the output
  Output
}

lying_source <- function(goodSources, lyingPi = seq(0.1, 0.3, by = 0.1),
                         lyingMu = seq(0.1, 1, by = 0.1),
                         minSigmaHiddenProcess = 0.1,
                         maxSigmaHiddenProcess = 1) {
  
  ### A function to explore the effect of a single dishonest source among a
  ### number of honest sources.
  
  # Initialize output matricies
  Output <- list(Brier = matrix(nrow = length(lyingPi), ncol = length(lyingMu)),
                 RMSE = matrix(nrow = length(lyingPi), ncol = length(lyingMu)),
                 AUC = matrix(nrow = length(lyingPi), ncol = length(lyingMu)))
  
  for(i in 1:length(lyingPi)) {
    for(j in 1:length(lyingMu)) {
      # Generate hidden process realizations
      hiddenData <- lapply(1:500,
                           function(x) synthetic_data(100,
                                                      runif(1,
                                                            min = minSigmaHiddenProcess,
                                                            max = maxSigmaHiddenProcess)))
      
      # Learning and transfer for honest sources
      learnedData <- lapply(hiddenData,
                            function(x) multi_learn(Data = x,
                                                    goodSources = goodSources))
      
      # Learning and transfer for bad source
      lyingData <- lapply(hiddenData,
                          function(x) learn_and_transfer(x,
                                                         π = lyingPi[i],
                                                         sourceμ = lyingMu[j],
                                                         callFromExp2 = TRUE))
      
      # Take the median of good and bad source reporting at each time step
      combinedData <- lapply(1:500,
                             function(x) cbind(learnedData[[x]],
                                               lyingData[[x]]))
      medianData <- lapply(combinedData, function(x) apply(x, 1, mod_median))
      
      # Find and eliminate any instances in which no forecast was generated because
      # the source did not learn any evidence
      medianDataLength <- sapply(medianData, length)
      medianIndex <- which(medianDataLength != 0)
      medianData <- medianData[medianIndex]
      
      # Generate forecasts
      forecastList <- lapply(medianData, generate_forecast)
      
      # Compute measure of performance
      evalList <- lapply(1:500,
                            function(x) compute_measures_performance(hiddenData[[x]],
                                                                     forecastList[[x]]))
      brierVec <- sapply(evalList, function(x) x$Brier)
      SEVec <- sapply(evalList, function(x) x$SE)
      
      # For the ROC curve, first collapse the ROC data into a matrix, then build a
      # list of four matricies for each of the possible outcomes, then take rowwise
      # sums through each matrix to compute the values needed for TPR and FPR.
      ROCMat <- sapply(evalList, function(x) x$outcomeType)
      ROCTypes <- lapply(c('truePos',
                           'trueNeg',
                           'falsePos',
                           'falseNeg'),
                         function(x) ROCMat == x)
      outcomeBreakout <- lapply(ROCTypes, function(x) apply(x, 1, sum))
      TPR <- outcomeBreakout[[1]] / (outcomeBreakout[[1]] + outcomeBreakout[[4]])
      FPR <- outcomeBreakout[[3]] / (outcomeBreakout[[3]] + outcomeBreakout[[2]])
      
      # Compute the area under the ROC curve using the auc function from the flux
      # package
      AUCval <- auc(FPR, TPR)
      
      Output$Brier[i,j] = mean(brierVec)
      Output$RMSE[i,j] = sqrt(mean(SEVec))
      Output$AUC[i,j] = AUCval
    }
  }
  Output
}

mod_median <- function(Vector) {
  # A varient of the median that first turns values of 0 into NAs. This is
  # necessary in order to disregard elements of the learned evidence matrix
  # in lying_source where no learning and reporting happened.
  
  if(sum(Vector == 0) == length(Vector)) return(0)
  Vector[which(Vector == 0)] <- NA
  median(Vector, na.rm = TRUE)
}

multi_learn <- function(Data, goodSources, minHonestPi = 0.05,
                        maxHonestPi = 0.3,
                        minHonestSigma = 0.05,
                        maxHonestSigma = 0.3) {
  sapply(1:goodSources, function(x) learn_and_transfer(Data,
                                                       π = runif(1, min = minHonestPi,
                                                                 max = maxHonestPi),
                                                       sourceσ = runif(1, min = minHonestSigma,
                                                                       max = maxHonestSigma),
                                                       callFromExp2 = TRUE))
}

learn_forecast_evaluate_single <- function(dataDF, runs, Outcome, Sources = 1) {
  # A wrapper function for the functions above. Takes as input a list
  # of data frames containing the synthetic data and inputs to the function
  # learn_and_transfer. Returns a list of five entries: Brier score for the
  # system, RMSE for the system, the system's ROC broken into the TPR and
  # FPR, and the area under the ROC curve.
  
  # Conduct vectorized learning and transfer of information from single source
  # to single collector.
  totalRuns <- runs * Sources
  
  learnData <- lapply(1:totalRuns, function(x) learn_and_transfer(dataDF, 
                                                             π = runif(1, 0.1, 0.5),
                                                             sourceσ = runif(1, 0, 0.3)))
  
  if(Sources > 1) {
    learnMatrix <- matrix(unlist(learnData), nrow = 100, ncol = totalRuns)
    learnStart <- 1:runs * Sources - Sources + 1
    learnEnd <- learnStart + Sources - 1
    splitMatrix <- lapply(1:runs,
                          function(x) learnMatrix[,learnStart[x]:learnEnd[x]])
    learnData <- lapply(splitMatrix, function(x) apply(x, 1, mod_median))
  }
  
  # Find and eliminate any instances in which no forecast was generated because
  # the source did not learn any evidence
  learnDataLength <- sapply(learnData, length)
  learnIndex <- which(learnDataLength != 0)
  learnData <- learnData[learnIndex]
  
  # Generate a forecast from each set of learned evidence
  forecastList <- lapply(learnData, generate_forecast)
  
  # Generate evaluate data for each forecast
  lengthData <- length(learnData)
  evalList <- lapply(1:lengthData,
                     function(x) compute_measures_performance(dataDF,
                                                              forecastList[[x]],
                                                              Outcome = Outcome))
  
  # Go through the resulting list, cull and compile the evaluation data into
  # vectors and matricies as needed for further reporting
  brierVec <- sapply(evalList, function(x) x$Brier)
  SEVec <- sapply(evalList, function(x) x$SE)
  
  # For the ROC curve, first collapse the ROC data into a matrix, then build a
  # list of four matricies for each of the possible outcomes, then take rowwise
  # sums through each matrix to compute the values needed for TPR and FPR.
  ROCMat <- sapply(evalList, function(x) x$outcomeType)
  ROCTypes <- lapply(c('truePos',
                       'trueNeg',
                       'falsePos',
                       'falseNeg'),
                     function(x) ROCMat == x)
  outcomeBreakout <- lapply(ROCTypes, function(x) apply(x, 1, sum))
  TPR <- outcomeBreakout[[1]] / (outcomeBreakout[[1]] + outcomeBreakout[[4]])
  FPR <- outcomeBreakout[[3]] / (outcomeBreakout[[3]] + outcomeBreakout[[2]])
  
  # Compute the area under the ROC curve using the auc function from the flux
  # package
  NaNTest <- (FPR + TPR) %>% sum
  if(!is.nan(NaNTest)) {
    AUC <- auc(FPR, TPR)
  } else {
    AUC <- NA
  }
  
  # Return a list
  list(Brier = mean(brierVec),
       RMSE = sqrt(mean(SEVec)),
       TPR = TPR,
       FPR = FPR,
       AUC = AUC)
}