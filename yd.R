library(survival)
library(relsurv)
library(latex2exp)

nessie_spi <- function(formula = formula(data), data, ratetable = relsurv::slopop, 
                       tis, starting.time, include.censoring=FALSE,
                       arg.example=FALSE, rmap){
  data_orig <- data
  call <- match.call()
  if (!missing(rmap)) {
    rmap <- substitute(rmap)
  }
  na.action <- NA
  rform <- relsurv:::rformulate(formula, data, ratetable, na.action, 
                                rmap)
  data <- rform$data
  data$Xs <- rep(1, nrow(data))
  n_rows <- nrow(data)
  
  # Fix demographic covariates:
  if(starting.time == "left.truncated"){
    rform$R[,"year"] <- rform$R[,"year"] - rform$R[,"age"]
    rform$R[,"age"] <- 0
  }
  if(include.censoring){
    # browser()
    wh <- which(rform$status==1)
    rform$Y[wh] <- max(rform$Y)
    
    if(arg.example){
      wh2 <- which(rform$status==1 & data$age==18262)
      rform$Y[wh2] <- 1826
    }
  }
  else{
    rform$Y <- rep(max(rform$Y), length(rform$Y))
    # status is not relevant in this case
  }
  
  out <- NULL
  out$yi <- NULL
  out$yidli <- NULL
  l_tis <- length(tis)
  temps <- lapply(1:n_rows, function(inx) {
    temp <- relsurv:::exp.prep(rform$R[inx, , drop = FALSE], rform$Y[inx], rform$ratetable, 
                               rform$status[inx], times = tis, fast = TRUE, cmp=FALSE,ys=data$start[inx])
    s_pi <- exp(-cumsum(temp$yidli))
    
    s_pi_helper <- which.min(temp$yidli==0)-1
    if(s_pi_helper>1){ s_pi[1:s_pi_helper] <- 0}
    
    if(include.censoring){ s_pi[(s_pi_helper+1):l_tis] <- pmin(s_pi[(s_pi_helper+1):l_tis], 
                                                               temp$yi[(s_pi_helper+1):l_tis])}
    
    c(s_pi, # s_pi
      temp$yidli*s_pi) # l_pi * s_pi
  })
  
  temps2 <- do.call("cbind", temps)
  
  temps2 <- rowSums(temps2)
  
  out$yi <- temps2[1:(length(temps2)/2)]
  out$yidli <- temps2[(length(temps2)/2+1):length(temps2)]
  return(out)
}

colVars <- function(x, na.rm = FALSE){
  f <- function(v, na.rm = na.rm) {
    if(is.numeric(v) || is.logical(v) || is.complex(v))
      var(v, na.rm = na.rm)
    else NA 
  }
  return(unlist(lapply(x, f, na.rm = na.rm)))
}


# Main function: 
# A function that takes a dataset and returns the 
# cum. inc. function on the data, the population ones and the YD
yl <- function(data, starting.time=c("left.truncated", "zero"), 
               ratetable=relsurv::slopop, exact.hazards=FALSE, find.cond.time=FALSE,
               lt.point, pop.curve=c("F_P_Spi", "F_P_Spi2", "F_P", "F_P_final", "F_P2", "all"),
               precision=15, admin.cens,
               arg.example=FALSE,
               timefix=FALSE,
               method=c('YD', 'YL2017', 'YL2013'),
               bootstrap=FALSE,
               B=10,
               add.times,
               cause.val,
               formula.arg=formula(data),
               is.boot=FALSE,
               first.boot=FALSE
){
  # data: dataset
  # starting.time: whether left-truncated times (if present at all) should be taken into account
  # ratetable: mortality tables
  # exact.hazards: calculate hazards on a daily basis (to be checked)
  # find.cond.time: if TRUE, return time at which there are at least 5 individuals in the at-risk set.
  # lt.point: fit the models conditional on time lt.point.
  # pop.curve: which estimator should be used for calculating the pop. cum. incidence curve
  # precision: the maximum number of days at which the population curve is evaluated. If time between events is bigger than precision, an in-between point is added at which the pop. curve is evaluated.
  # admin.cens: if not defined, administrative censoring is not taken into account. If a Date is supplied administrative censoring is taken until that time. Works only if starting.time=="left.truncated".
  # arg.example: temporary argument, used for checking additionalities
  # timefix: define timefix in survfit (for calculating the observed curve). Default is TRUE.
  
  starting.time <- match.arg(starting.time)
  pop.curve <- match.arg(pop.curve)
  method <- match.arg(method)
  
  data_orig <- data
  out <- NULL
  late.values <- FALSE
  
  # if(starting.time=="left.truncated"){
  if(!missing(admin.cens)){
    if(class(admin.cens)!='Date') warning('Object of class Date should be supplied to admin.cens.')
    end_date <- data$year+(data$stop-data$age)
    if(any(end_date > admin.cens)) warning('There are events that occur after the date of administrative censoring. Please check the values in arguments data and admin.cens.')
    id_admin_cens <- which(admin.cens==end_date)
  }
  # }
  
  starting_age <- rep(0,nrow(data))
  if(starting.time == 'left.truncated'){
    starting_age <- data$age
    formula_basic <- Surv(age, stop, status)~1
  } else{
    formula_basic <- Surv(stop-age, status)~1
  }
  starting_age <- as.numeric(starting_age)
  
  # CIF on data:
  
  if(any(data$age>=data$stop)) browser()
  
  if(missing(formula.arg)){
    mod <- survfit(formula_basic, data=data, timefix=timefix)
  } else{
    mod <- survfit(as.formula(formula.arg), data=data, timefix=timefix, id = 1:nrow(data))
  }
  
  surv_obj <- as.character(as.formula(formula.arg)[[2]])
  if('mstate' %in% surv_obj){
    surv_obj_new <- paste0(surv_obj[1], '(', surv_obj[2], ',', surv_obj[3])
    if(length(surv_obj)==5){
      surv_obj_new <- paste0(surv_obj_new, ',', surv_obj[4], ')')
    } else{
      surv_obj_new <- paste0(surv_obj_new, ')')
    }
    formula.arg <- paste0(surv_obj_new, '~1')
  }
  surv_obj <- as.character(as.formula(formula.arg)[[2]])
  status_obj <- surv_obj[length(surv_obj)]
  
  
  if(!missing(cause.val)){
    mod$n.risk <- mod$n.risk[,1]
    mod$n.event <- mod$n.event[,cause.val+1]
    mod$surv <- 1-mod$pstate[,cause.val+1]
    mod$std.err <- mod$std.err[,cause.val+1]
    mod$cumhaz <- mod$cumhaz[,cause.val]
  }
  
  
  
  if(!missing(add.times)){
    mod_sum <- summary(mod, times = sort(unique(c(mod$time, add.times))))
    if(any(!(add.times %in% mod_sum$time))){
      if(!is.boot){
        if(!first.boot){
          warning('Some values in add.times are after the last follow-up time. All measures are extrapolated up to these times. Please consider removing them.')
        } 
        late.values <- TRUE
        
        miss_tajms <- add.times[!(add.times %in% mod_sum$time)]
        mod_sum$time <- c(mod_sum$time, miss_tajms)
        mod_sum$n.risk <- c(mod_sum$n.risk, rep(mod_sum$n.risk[length(mod_sum$n.risk)], length(miss_tajms)))
        mod_sum$n.event <- c(mod_sum$n.event, rep(0, length(miss_tajms)))
        mod_sum$surv <- c(mod_sum$surv, rep(mod_sum$surv[length(mod_sum$surv)], length(miss_tajms)))
        mod_sum$cumhaz <- c(mod_sum$cumhaz, rep(mod_sum$cumhaz[length(mod_sum$cumhaz)], length(miss_tajms)))
        
        # First fix std.err:
        if(is.nan(mod_sum$std.err[length(mod_sum$std.err)])){
          mod_sum$std.err[length(mod_sum$std.err)] <- mod_sum$std.err[length(mod_sum$std.err) - 1]
        }
        mod_sum$std.err <- c(mod_sum$std.err, rep(mod_sum$std.err[length(mod_sum$std.err)], length(miss_tajms)))
      }
    }
    mod$time <- mod_sum$time
    mod$n.risk <- mod_sum$n.risk
    mod$n.event <- mod_sum$n.event
    mod$surv <- mod_sum$surv
    mod$std.err <- mod_sum$std.err
    mod$cumhaz <- mod_sum$cumhaz
  }

  if(find.cond.time) return(mod$time[which.min(mod$n.risk<5)])
  
  # Add conditional probabilities:
  if(!missing(lt.point)){
    # Weight the survivals:
    mod$surv <- mod$surv/summary(mod, times = lt.point)$surv
    # Then the cond. cum. function = 1 - cond. survival.
    
    # Limit on relevant times:
    mod$surv <- mod$surv[mod$time>=lt.point]
    mod$time <- mod$time[mod$time>=lt.point]
  }
  
  # Calculate AUC:
  if(length(mod$time)>1){
    # browser()
    survs <- c(1, mod$surv[1:(length(mod$surv)-1)])
    auc_data <- sum(diff(c(0, mod$time))*(1 - survs))
  } else{
    auc_data <- mod$time*mod$surv
  }
  
  out$F_data <- 1-mod$surv
  out$auc_data <- auc_data/365.241
  
  if(exact.hazards){
    mod$time <- seq(min(mod$time), max(mod$time), by=1)
    mod$surv <- exp(-cumsum(rep(ratetable[1,1,1], max(mod$time)-min(mod$time)+1)))
    
    out$F_data <- 1-exp(-cumsum(c(0, rep(ratetable[1,1,1], max(mod$time)-min(mod$time)))))
    out$auc_data <- sum(out$F_data)/365.241
  }
  
  ###
  if(method %in% c('YL2017', 'YL2013')){
    # YL_O:
    if(starting.time=="left.truncated"){
      it_auc <- rep(NA, nrow(data))
      mod_sum <- summary(mod, times=unique(sort(c(data$age, data$stop))))
      for(it in 1:nrow(data)){
        it_wh <- which(data$age[it] == mod_sum$time)
        it_surv <- mod_sum$surv[it_wh:length(mod_sum$surv)]/mod_sum$surv[it_wh]
        it_auc[it] <- sum(c(0, diff(mod_sum$time[it_wh:length(mod_sum$time)]))*(1 - it_surv))/365.241
      }
      YL_O <- mean(it_auc)
    } else{
      YL_O <- out$auc_data
    } 
    
    # YL_P:
    data_yi <- data
    
    rform <- relsurv:::rformulate(formula_basic, data, ratetable, na.action=na.omit)
    data <- rform$data
    
    # Check covariates:
    p <- rform$m
    if (p > 0) stop("There shouldn't be any covariates in the formula. This function gives non-parametric estimates of the hazards.")
    else data$Xs <- rep(1, nrow(data)) #if no covariates, just put 1
    
    out_n <- table(data$Xs) #table of strata
    out$time <- out$haz.excess <- out$haz.pop <- out$std.err <- out$strata <-  NULL
    
    kt <- 1 # the only stratum
    inx <- which(data$Xs == names(out_n)[kt]) #individuals within this stratum
    # tis <- sort(unique(rform$Y[inx])) #unique times
    if(starting.time == "zero") tis <- sort(unique(c(rform$Y[inx], seq(1, max(rform$Y[inx]), precision)))) #unique times
    else tis <- sort(unique(c(rform$Y[inx], data$age, seq(min(data$age), max(rform$Y[inx], data$age), precision)))) #unique times
    # Added 2 monthly times between entries and event times
    
    if(!missing(add.times)){
      tis <- sort(unique(c(tis, add.times)))
    }
    
    # Fix demographic covariates:
    if(starting.time == "left.truncated"){
      rform$R[,"year"] <- rform$R[,"year"] - rform$R[,"age"]
      rform$R[,"age"] <- 0
    }
    it_auc_P <- rep(NA, nrow(data))
    
    if(method == 'YL2017'){
      for(it in 1:nrow(data)){
        temp <- relsurv:::exp.prep(rform$R[it,,drop=FALSE],max(rform$Y),rform$ratetable,rform$status[it],times=tis,fast=FALSE, cmp=FALSE, ys=starting_age[it], netweiDM = FALSE)
        # temp <- relsurv:::exp.prep(rform$R[inx,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status[inx],times=tis2,fast=FALSE, cmp=FALSE, ys=starting_age, netweiDM = TRUE)
        if(starting.time == "left.truncated"){
          it_wh <- which(data$age[it] == tis)
          hazs <- temp$yidli[it_wh:length(tis)]
          hazs[1] <- 0
          cumhazs <- cumsum(hazs)
          F_P <- 1 - exp(-cumhazs)
          it_auc_P[it] <- sum(c(tis[it_wh], diff(tis[it_wh:length(tis)]))*c(0, F_P[1:(length(F_P)-1)]))/365.241
        } else{
          # it_wh <- which(data$age[it] == tis)
          hazs <- temp$yidli[1:length(tis)]
          hazs[1] <- 0
          cumhazs <- cumsum(hazs)
          F_P <- 1 - exp(-cumhazs)
          it_auc_P[it] <- sum(c(0, diff(tis))*c(0, F_P[1:(length(F_P)-1)]))/365.241
        }
        
      }
      YL_P <- mean(it_auc_P)
      
      YL=YL_O-YL_P
    } else{
      # browser()
      temp <- relsurv:::exp.prep(rform$R[,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status,times=tis, fast=TRUE, cmp=FALSE, ys=starting_age)
      # temp <- relsurv:::exp.prep(rform$R[,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status,times=mod$time, fast=TRUE, cmp=FALSE, ys=starting_age)
      
      temp$yi[temp$yi==0] <- Inf
      
      out$time <- c(out$time, tis)						#add times

      # Calculate hazards:
      haz.pop <- temp$yidli/temp$yi
      
      out$haz.pop <- c(out$haz.pop,haz.pop)
      out$cum.haz.pop <- cumsum(out$haz.pop)
      
      mod_tis <- summary(mod, times = tis)

      F_E <- cumsum(mod_tis$surv*(mod_tis$n.event/mod_tis$n.risk - haz.pop)*c(0, diff(tis))/365.241)

      YL <- cumsum(F_E*c(0, diff(tis))/365.241)
      
      return(YL)
      
    }
    
    return(c(YL_O=YL_O, YL_P=YL_P, YL=YL))
  }
  
  ################################################### #
  ## Prava varianca:
  times_all <- c(mod$time[1], diff(mod$time))/365.241
  times_all2 <- c(0, diff(mod$time))/365.241
  surv_all <- c(1, mod$surv[1:(length(mod$surv)-1)])
  auc_all <- cumsum(times_all2*surv_all)
  out$auc_data_var1 <- sum(((auc_all[length(auc_all)] - auc_all)^2*mod$n.event)/(mod$n.risk*(mod$n.risk - mod$n.event)), na.rm=T)
  obs_var_time <- sapply(1:length(auc_all), function(x) {
    numer <- mod$n.risk[1:x]*(mod$n.risk[1:x] - mod$n.event[1:x])
    numer[numer==0] <- Inf
    sum(((auc_all[x] - auc_all[1:x])^2*mod$n.event[1:x])/numer)
  })
  if(is.nan(obs_var_time[length(obs_var_time)])){
    obs_var_time[length(obs_var_time)] <- obs_var_time[length(obs_var_time)-1]
  }
  ################################################### #
  
  # CIF on population:
  
  # Take into account conditional probabilities in the data:
  if(!missing(lt.point)){
    data <- subset(data, stop>lt.point)
    data$age <- ifelse(data$age<lt.point, lt.point, data$age)
    starting_age <- data$age
    starting_age <- as.numeric(starting_age)
  }
  
  data_yi <- data
  if(any(data$age>=data$stop)) browser()

  rform <- relsurv:::rformulate(as.formula(formula_basic), data, ratetable, na.action=na.omit)
  data <- rform$data
  
  # Check covariates:
  p <- rform$m
  if (p > 0) stop("There shouldn't be any covariates in the formula. This function gives non-parametric estimates of the hazards.")
  else data$Xs <- rep(1, nrow(data)) #if no covariates, just put 1
  
  out_n <- table(data$Xs) #table of strata
  out$time <- out$haz.excess <- out$haz.pop <- out$std.err <- out$strata <-  NULL
  
  kt <- 1 # the only stratum
  inx <- which(data$Xs == names(out_n)[kt]) #individuals within this stratum
  if(starting.time == "zero") tis <- sort(unique(c(rform$Y[inx], seq(1, max(rform$Y[inx]), precision)))) #unique times
  else tis <- sort(unique(c(rform$Y[inx], data$age, seq(min(data$age), max(rform$Y[inx], data$age), precision)))) #unique times
  # Added 2 monthly times between entries and event times
  
  if(!missing(add.times)){
    tis <- sort(unique(c(tis, add.times)))
  }
  
  # Fix demographic covariates:
  if(starting.time == "left.truncated"){
    rform$R[,"year"] <- rform$R[,"year"] - rform$R[,"age"]
    rform$R[,"age"] <- 0
  }
  
  if(pop.curve=='F_P' | pop.curve=="all"){
  
    if(any(rform$Y[inx]<=starting_age)) browser()
    temp <- relsurv:::exp.prep(rform$R[inx,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status[inx],times=tis,fast=TRUE, cmp=FALSE, ys=starting_age)
    temp$yi[temp$yi==0] <- Inf
    
    out$time <- c(out$time, tis)						#add times

    # Calculate hazards:
    haz.pop <- temp$yidli/temp$yi
    out$haz.pop <- c(out$haz.pop,haz.pop)
    out$cum.haz.pop <- cumsum(out$haz.pop)
    out$F_P <- 1-exp(-out$cum.haz.pop)
    out$auc_pop <- sum(c(tis[1], diff(tis))*c(0, out$F_P[1:(length(out$F_P)-1)]))/365.241
    
  } 
  data_spi2 <- data
  
  if(pop.curve=='F_P_Spi2' | pop.curve=="all"){
    
    if(any(data_spi2$start>=data_spi2$Y)) browser()
    exp.surv2 <- nessie_spi(Surv(start, Y, stat)~1, data=data_spi2, ratetable=ratetable, 
                            tis=tis, starting.time=starting.time, include.censoring = TRUE,
                            arg.example)
    # browser()
    out$haz.pop.spi2 <- exp.surv2$yidli/exp.surv2$yi
    out$cum.haz.pop.spi2 <- cumsum(out$haz.pop.spi2)
    out$F_P_Spi2 <- 1-exp(-out$cum.haz.pop.spi2)
    # out$auc_pop_Spi <- sum(c(tis[1], diff(tis))*out$F_P_Spi)/365.241
    out$auc_pop_Spi2 <- sum(c(tis[1], diff(tis))*c(0, out$F_P_Spi2[1:(length(out$F_P_Spi2)-1)]))/365.241
  } 
  if(pop.curve=='F_P_Spi' | pop.curve=="all"){
    if((!missing(admin.cens))){
      data_spi2$stat <- 1
      data_spi2$stat[id_admin_cens] <- 0
      exp.surv <- nessie_spi(Surv(start, Y, stat)~1, data=data_spi2, ratetable=ratetable, 
                             tis=tis, starting.time=starting.time, include.censoring = TRUE,
                             arg.example)
    } else{
      # Don't take into account censoring:
      exp.surv <- nessie_spi(Surv(start, Y, stat)~1, data=data_spi2, ratetable=ratetable, 
                             tis=tis, starting.time=starting.time, include.censoring = FALSE,
                             arg.example)
    }
    
    out$haz.pop.spi <- exp.surv$yidli/exp.surv$yi
    out$cum.haz.pop.spi <- cumsum(out$haz.pop.spi)
    out$F_P_Spi <- 1-exp(-out$cum.haz.pop.spi)
    # out$auc_pop_Spi <- sum(c(tis[1], diff(tis))*out$F_P_Spi)/365.241
    out$auc_pop_Spi <- sum(c(tis[1], diff(tis))*c(0, out$F_P_Spi[1:(length(out$F_P_Spi)-1)]))/365.241
  }
  
  if(pop.curve=='F_P_final'){
    # Shift all to the end:
    if(starting.time == "left.truncated") data_yi$stop <- max(data_yi$stop)
    
    rform2 <- rform
    if(any(data_yi$age>=data_yi$stop)) browser()
    
    rform <- relsurv:::rformulate(formula_basic, data_yi, ratetable, na.action=na.omit)
    
    # Shift all to the end:
    if(starting.time == "zero"){
      rform$Y <- rep(max(rform$Y), length(rform$Y))
      rform$data[,"Y"] <- rform$Y
    } 
    data <- rform$data    
    
    # Check covariates:
    p <- rform$m
    if (p > 0) stop("There shouldn't be any covariates in the formula. This function gives non-parametric estimates of the hazards.")
    else data$Xs <- rep(1, nrow(data)) #if no covariates, just put 1
    
    out$haz.pop2 <- NULL
    
    kt <- 1 # the only stratum
    inx <- which(data$Xs == names(out_n)[kt]) #individuals within this stratum
    tis2 <- tis

    # Fix demographic covariates:
    if(starting.time == "left.truncated"){
      rform$R[,"year"] <- rform$R[,"year"] - rform$R[,"age"]
      rform$R[,"age"] <- 0
    }
    
    if(any(starting_age>=rform$Y[inx])) browser()
    temp <- relsurv:::exp.prep(rform$R[inx,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status[inx],times=tis2,fast=FALSE, cmp=FALSE, ys=starting_age, netweiDM = TRUE)
    temp$sidliD[1] <- 0
    # temp$sisD[1] <- 1
    temp$sisD[temp$sisD==0] <- Inf
    # }
    haz.pop2 <- temp$sidliD/temp$sisD
    
    out$haz.pop2 <- c(out$haz.pop2, haz.pop2)
    out$cum.haz.pop2 <- cumsum(out$haz.pop2)
    out$F_P2 <- 1-exp(-out$cum.haz.pop2)
    # out$auc_pop2 <- sum(c(tis2[1], diff(tis2))*out$F_P2)/365.241
    out$auc_pop2 <- sum(c(tis2[1], diff(tis2))*c(0, out$F_P2[1:(length(out$F_P2)-1)]))/365.241
    
    out$sidli <- temp$sidli
    out$sis <- temp$sis
    
    # DODATEK:
    haz.pop.ves.cas <- temp$sidli
    haz.pop.ves.cas[1] <- 0
    haz.pop.ves.cas <- haz.pop.ves.cas/temp$sis
    out$cum.haz.pop.ves.cas <- cumsum(haz.pop.ves.cas)
    out$F_P_ves_cas <- 1 - exp(-out$cum.haz.pop.ves.cas)
    out$auc_pop_ves_cas <- sum(c(tis2[1], diff(tis2))*c(0, out$F_P_ves_cas[1:(length(out$F_P_ves_cas)-1)]))/365.241
  }
  
  if(pop.curve=='F_P2' | pop.curve=="all"){
    # Shift all to the end:
    if(starting.time == "left.truncated") data_yi$stop <- max(data_yi$stop)
    
    rform2 <- rform
    if(any(data_yi$age>=data_yi$stop)) browser()
    
    rform <- relsurv:::rformulate(formula_basic, data_yi, ratetable, na.action=na.omit)
    
    # Shift all to the end:
    if(starting.time == "zero"){
      rform$Y <- rep(max(rform$Y), length(rform$Y))
      rform$data[,"Y"] <- rform$Y
    } 
    data <- rform$data    
    
    # Check covariates:
    p <- rform$m
    if (p > 0) stop("There shouldn't be any covariates in the formula. This function gives non-parametric estimates of the hazards.")
    else data$Xs <- rep(1, nrow(data)) #if no covariates, just put 1
    
    out$haz.pop2 <- NULL
    
    kt <- 1 # the only stratum
    inx <- which(data$Xs == names(out_n)[kt]) #individuals within this stratum
    tis2 <- tis
    # tis2 <- sort(unique(rform$Y[inx])) #unique times
    
    # Fix demographic covariates:
    if(starting.time == "left.truncated"){
      rform$R[,"year"] <- rform$R[,"year"] - rform$R[,"age"]
      rform$R[,"age"] <- 0
    }
    
    if(any(starting_age>=rform$Y[inx])) browser()
    
    # temp <- relsurv:::exp.prep(rform$R[inx,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status[inx],times=tis2,fast=TRUE, cmp=FALSE, ys=0)
    temp <- relsurv:::exp.prep(rform$R[inx,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status[inx],times=tis2,fast=TRUE, cmp=FALSE, ys=starting_age)
    
    # Fix at-risk process, if needed:
    temp$yi[temp$yi==0] <- Inf
    
    # Calculate hazards:
    haz.pop2 <- temp$yidli/temp$yi
    
    out$haz.pop2 <- c(out$haz.pop2, haz.pop2)
    out$cum.haz.pop2 <- cumsum(out$haz.pop2)
    out$F_P2 <- 1-exp(-out$cum.haz.pop2)
    # out$auc_pop2 <- sum(c(tis2[1], diff(tis2))*out$F_P2)/365.241
    out$auc_pop2 <- sum(c(tis2[1], diff(tis2))*c(0, out$F_P2[1:(length(out$F_P2)-1)]))/365.241
  }
  
  ###
  # Bootstrap:
  if(bootstrap){
    # browser()
    data_b <- data_orig
    data_b$id <- 1:nrow(data_b)
    yl_boot <- ylboot(theta=ylboot.iter, data=data_b, id="id",
                      B=B, verbose=0, #all_times = all_times,
                      rmap = rmap, #time.format = time.format.orig, 
                      ratetable=ratetable#, add.times=add.times
                      , starting.time, pop.curve, precision,
                      add.times = add.times
    )
    L_OP <- yl_boot[[3]]
    F_boot <- yl_boot[[2]]
    yl_boot <- as.data.frame(t(yl_boot[[1]]))
  }
  ###
  pop.curve.orig <- pop.curve
  if(pop.curve=='F_P_final') pop.curve = 'F_P2'
  
  out$strata <- c(out$strata, length(tis))				#number of times in this strata
  names(out$strata) <-  names(out_n)
  out$strata <-  NULL
  out$auc <- c(auc_data=out$auc_data, auc_pop=out$auc_pop, auc_pop2=out$auc_pop2, auc_pop_Spi=out$auc_pop_Spi, auc_pop_Spi2=out$auc_pop_Spi2)
  
  if(pop.curve=='all'){
    F_P_final <- data.frame(time=out$time,F_P=out$F_P, F_P2=out$F_P2, F_P_Spi=out$F_P_Spi, F_P_Spi2=out$F_P_Spi2)
  } else if(pop.curve=='F_P'){
    F_P_final <- data.frame(time=tis,F_P=out$F_P)
  } else if(pop.curve=='F_P2'){
    F_P_final <- data.frame(time=tis,F_P=out$F_P2)
  } else if(pop.curve=='F_P_Spi'){
    F_P_final <- data.frame(time=tis,F_P=out$F_P_Spi)
  } else if(pop.curve=='F_P_Spi2'){
    F_P_final <- data.frame(time=tis,F_P=out$F_P_Spi2)
  } 
  
  # YD through time:
  F_data_yd <- data.frame(time=mod$time, F_data=out$F_data)
  yd_data <- cumsum(c(F_data_yd$time[1], diff(F_data_yd$time))*c(0, F_data_yd$F_data[1:(nrow(F_data_yd)-1)]))/365.241
  
  F_P_yd <- F_P_final
  yd_pop <- cumsum(c(F_P_yd$time[1], diff(F_P_yd$time))*c(0, F_P_yd$F_P[1:(nrow(F_P_yd)-1)]))/365.241
  yd_pop <- yd_pop[F_P_final$time %in% mod$time]
  yd_curve <- data.frame(time=mod$time, yd=yd_data - yd_pop, 
                         obs_var=obs_var_time,
                         # obs_var22=obs_var_time22,
                         yd_data=yd_data,
                         yd_pop=yd_pop
  )
  ###
  # Add values at time zero:
  F_data_tmp <- data.frame(time=mod$time,
                           F_data=out$F_data)
  F_tmp <- F_data_tmp[1,]
  F_tmp$time <- min(starting_age)
  F_tmp$F_data <- 0
  if(!(F_tmp$time %in% F_data_tmp$time)) F_data_tmp <- rbind(F_tmp, F_data_tmp)
  
  yd_curve_tmp <- yd_curve[1,]
  yd_curve_tmp$time <- min(starting_age)
  yd_curve_tmp[,2:ncol(yd_curve_tmp)] <- 0
  if(!(yd_curve_tmp$time %in% yd_curve$time)) yd_curve <- rbind(yd_curve_tmp, yd_curve)
  
  if(bootstrap){
    yd_curve$boot_var <- colVars(yl_boot, na.rm=TRUE)
    if(late.values){
      last_val <- tail(yd_curve$boot_var[!is.na(yd_curve$boot_var)],1)
      yd_curve$boot_var[is.na(yd_curve$boot_var)] <- last_val
    }
    yl_sd_boot <- sd(yl_boot[, ncol(yl_boot)], na.rm=TRUE)
  } 
  
  return_obj <- list(F_data=F_data_tmp,
                     F_P=F_P_final,
                     auc=out$auc,
                     yd_curve=yd_curve,
                     starting.time=starting.time,
                     pop.curve=pop.curve.orig,
                     out=out
  )
  
  if(bootstrap){
    return_obj[[length(return_obj)+1]] <- F_boot
    names(return_obj)[length(return_obj)] <- 'F_boot'
    return_obj[[length(return_obj)+1]] <- L_OP
    names(return_obj)[length(return_obj)] <- 'L_OP'
    return_obj <- append(return_obj, yl_sd_boot)
    names(return_obj)[length(return_obj)] <- 'yl_sd_boot'
  } 
  
  return(return_obj)
}

# Bootstrap function:
ylboot <- function(theta, data, B = 5, id = "id", verbose = 0, 
                   #all_times, 
                   rmap, #time.format, 
                   ratetable=relsurv::slopop, #add.times, 
                   starting.time, pop.curve, precision,
                   add.times,
                   ...){
  ids <- unique(data[, id])
  n <- length(ids)
  if(!missing(add.times)){
    th <- ylboot.iter(data, starting.time = starting.time, pop.curve = pop.curve, precision = precision,
                      ratetable=ratetable, first=TRUE, add.times = add.times, ...)
  } else{
    th <- ylboot.iter(data, starting.time = starting.time, pop.curve = pop.curve, precision = precision,
                      ratetable=ratetable, first=TRUE, ...)
  }
  
  simple_par <- TRUE
  if(missing(add.times)) simple_par <- FALSE
  
  # Prepare objects:
  res <- data.frame(matrix(NA, nrow=B, ncol=nrow(th[[2]])))
  if(!missing(add.times)){
    # add.times2 <- add.times
  } else{
    add.times <- th[[1]]$time
  }
  
  Fdata <- data.frame(matrix(NA, nrow=B, ncol=length(add.times)))
  Fp <- data.frame(matrix(NA, nrow=B, ncol=length(add.times)))
  L_O <- data.frame(matrix(NA, nrow=B, ncol=length(add.times)))
  L_P <- data.frame(matrix(NA, nrow=B, ncol=length(add.times)))
  
  # Iteration:
  for (b in 1:B) {
    nek_obj <- ylboot.apply(b, verbose, ids, data, id, add.times, starting.time, pop.curve, precision, ratetable, th, simple_par, ...)
    res[b,1:length(nek_obj[[1]])] <- nek_obj[[1]]
    
    subnek <- subset(nek_obj[[2]], time %in% add.times)
    

    sub_vec <- 1:nrow(subnek)
    Fdata[b,sub_vec] <- subnek$F_data
    Fp[b,sub_vec] <- subnek$F_P
    
    subnek2 <- subset(nek_obj[[3]], time %in% add.times)
    
    sub2_vec <- 1:nrow(subnek2)
    L_O[b,sub2_vec] <- subnek2$yd_data
    L_P[b,sub2_vec] <- subnek2$yd_pop
  }
  res <- as.data.frame(t(res))
  
  if (verbose) 
    cat("\n")
  # res <- res[take_values]
  
  F_obj <- data.frame(time=add.times,
                      F_data=colVars(Fdata, na.rm = TRUE),
                      F_P=colVars(Fp, na.rm = TRUE))
  L_OP <- data.frame(time=add.times,
                     L_O=colVars(L_O, na.rm = TRUE),
                     L_P=colVars(L_P, na.rm = TRUE))
  
  return(list(res, F_obj, L_OP))
}

ylboot.apply <- function(b, verbose, ids, data, id, add.times, starting.time, pop.curve, precision, ratetable, th, simple_par,
                         ...){
  if (verbose > 0) {
    cat("\nBootstrap replication", b, "\n")
    flush.console()
  }
  bootdata <- NULL
  bids <- sample(ids, replace = TRUE)
  bidxs <- unlist(sapply(bids, function(x) which(x == 
                                                   data[, id])))
  bootdata <- data[bidxs, ]
  if (verbose > 0) {
    cat("applying theta ...")
  }
  
  if(length(unique(bootdata[,id]))==1){
    next
  } 
  
  if(!missing(add.times) & simple_par){
    add.times.arg <- sort(unique(c(th[[2]]$time, add.times)))
  } else{
    add.times.arg <- th[[2]]$time
  }
  add.times.arg2 <- add.times.arg
  # Remove unnecessary times
  if(starting.time == 'left.truncated'){
    add.times.arg <- add.times.arg[add.times.arg<=max(bootdata$stop)]
  } else{
    add.times.arg <- add.times.arg[add.times.arg<=max(bootdata$stop - bootdata$age)]
  }
  
  thstar <- ylboot.iter(bootdata, starting.time = starting.time, pop.curve = pop.curve, precision = precision,
                        ratetable=ratetable, add.times=add.times.arg, ...)
  thstar2 <- thstar
  L_OP <- thstar[[3]]
  Fobj <- thstar[[2]]
  thstar <- thstar[[1]]
  
  # print(b)
  if(nrow(th[[2]]) < nrow(thstar)){
    thstar <- thstar[thstar$time %in% th[[2]]$time, ]
    L_OP <- L_OP[L_OP$time %in% th[[2]]$time, ]
    Fobj <- Fobj[Fobj$time %in% th[[2]]$time, ]
  }
  
  # Ali kaksne vrednosti manjkajo:
  if(length(th[[2]]$time[th[[2]]$time <= max(thstar$time)]) != length(thstar$time)) browser()
  pogoj <- any(th[[2]]$time[th[[2]]$time <= max(thstar$time)] != thstar$time)
  if(pogoj){
    
    missing_times <- th[[2]]$time[which(!(th[[2]]$time %in% thstar$time))]
    
    if(length(missing_times)>0){
      # There are times missing in thstar, add them:
      add_df <- thstar[1:length(missing_times),]
      add_df$time <- missing_times
      add_df$yd <- NA
      add_df$obs_var <- NA
      add_df$yd_data <- NA
      
      thstar <- rbind(thstar, add_df)
      thstar <- thstar[order(thstar$time),] # redundantno
      
      thstar$yd <- mstate:::NAfix(thstar$yd, 0)
      thstar$obs_var <- mstate:::NAfix(thstar$obs_var, 0)
      thstar$yd_data <- mstate:::NAfix(thstar$yd_data, 0)
      
      if(nrow(th[[2]]) < nrow(thstar)){
        thstar <- thstar[thstar$time %in% th[[2]]$time, ]
      }
      
      if(nrow(th[[2]]) != nrow(thstar)) browser()      
    } else{ 
      # This means there's more times in thstar than needed. Remove unnecessary times:
      thstar <- thstar[-which(!(thstar$time %in% th[[2]]$time)),]
      L_OP <- L_OP[-which(!(L_OP$time %in% th[[2]]$time)),]
      Fobj <- Fobj[-which(!(Fobj$time %in% th[[2]]$time)),]
      
      if(nrow(th[[2]]) != nrow(thstar)) browser()
    } 
  }
  
  # thstar$b <- b
  # Save result: 
  # res[b,] <- 
  
  list(thstar$yd, Fobj, L_OP)
}

ylboot.iter <- function(data, #all_times,
                        starting.time, pop.curve, precision,
                        rmap, #time.format, 
                        ratetable=relsurv::slopop,
                        first=FALSE, add.times
){
  if(!missing(rmap))  rmap <- as.call(rmap)
  if(first){
    is.boot <- FALSE
    first.boot <- TRUE
  } else{
    is.boot <- TRUE
    first.boot <- FALSE
  }
  
  # Round, if needed:
  tolerance <- 1e-15
  
  if(missing(add.times)){
    object <- yl(data = data, starting.time = starting.time, ratetable = ratetable, 
                 pop.curve = pop.curve, precision=precision, bootstrap=FALSE, is.boot=is.boot, first.boot = first.boot)
  } else{
    object <- yl(data = data, starting.time = starting.time, ratetable = ratetable, 
                 pop.curve = pop.curve, precision=precision, bootstrap=FALSE, add.times=add.times, is.boot=is.boot, first.boot = first.boot)
  }
  
  if(first) return(list(object$yd_curve, object$F_data))
  else{
    # return(object$yd_curve)
    Fobj <- merge(object$F_data, object$F_P, by='time', all.x=TRUE)
    L_OP <- object$yd_curve[,c('time', 'yd_data', 'yd_pop')]
    return(list(object$yd_curve,
                Fobj,
                L_OP))
  } 
}



# Plotting function:
plot.yl <- function(yl,plot.all.curves=TRUE, plot.spi2=FALSE, admin, add.legend = T, ...){
  # yl: object given from the yl() function
  # plot.all.curves: if there are multiple pop. curves in yl, should they all be plotted?
  # plot.spi2: if there are multiple pop. curves in yl, should F_P_Spi2 be plotted?
  # admin: add F_P values of curve with administrative censoring
  
  if(yl$starting.time == "left.truncated") xlab_value <- "Age"
  else xlab_value <- "Time since entry"
  
  plot(yl$F_data$time/365.241, yl$F_data$F_data, 
       type="s", ylab="Cumulative incidence function", xlab=xlab_value, ylim=c(0,1),
       xlim=c(min(yl$F_P$time[1]), max(yl$F_data$time))/365.241, ...)
  
  
  legend_values <- c("F_data", "F_P", "F_P2", "F_P_Spi", "F_P_Spi2")
  legend_colors <- c("black", "red", "blue", "green", "purple")
  
  if(yl$pop.curve=='all'){
    if(plot.all.curves){
      lines(yl$F_P$time/365.241, yl$F_P$F_P, col="red", type='s')
      lines(yl$F_P$time/365.241, yl$F_P$F_P2, col="blue", type='s')
    } else{
      legend_values <- legend_values[!(legend_values %in% c("F_P","F_P2"))]
      legend_colors <- legend_colors[!(legend_colors %in% c("red","blue"))]
    }
    lines(yl$F_P$time/365.241, yl$F_P$F_P_Spi, col="green", type='s')
    if(plot.spi2){
      lines(yl$F_P$time/365.241, yl$F_P$F_P_Spi2, col="purple", type='s')
    } else{
      legend_values <- legend_values[!(legend_values %in% c("F_P_Spi2"))]
      legend_colors <- legend_colors[!(legend_colors %in% c("purple"))]
    }
  } else{
    find_col <- which(yl$pop.curve == legend_values)
    lines(yl$F_P$time/365.241, yl$F_P$F_P, col=legend_colors[find_col], type='s')
    
    legend_values <- legend_values[c(1, find_col)]
    legend_colors <- legend_colors[c(1, find_col)]
  }
  if (add.legend == T) {
    legend(x="topleft", legend_values, 
           col=legend_colors, lty=1)
  }
}

plot.helper <- function(yl, obj){
  
  df_poly <- data.frame(time=yl[[obj]]$time/365.241,
                        prob=yl[[obj]]$prob)
  df_st <- df_poly[1,]
  df_st$prob <- 0
  df_end <- df_poly[nrow(df_poly),]
  df_end$prob <- 0
  df_poly <- rbind(df_st, df_poly, df_end)
  
  df_poly
}

gg_color_hue <- function(n) {
  hues = seq(15, 375, length = n + 1)
  hcl(h = hues, l = 65, c = 100)[1:n]
}

plot.f.gg <- function(yl, xbreak, ybreak, xlimits, ylimits, show.legend=TRUE, ...){
  # yl: object given from the yl() function
  
  library(ggplot2)
  
  if(yl$starting.time == "left.truncated") xlab_value <- "Age"
  else xlab_value <- "Time since entry"
  
  colnames(yl$F_data)[2] <- 'prob'
  colnames(yl$F_P)[2] <- 'prob'
  out <- rbind(
    cbind(yl$F_data, Curve='Observed'),
    cbind(yl$F_P, Curve='Population')
  )
  
  if(missing(xlimits)){
    xlimits <- c(min(yl$F_P$time[1]), max(yl$F_data$time))/365.241
  }
  if(missing(ylimits)){
    ylimits <- c(0,max(out$prob))*1.1
  }
  
  # colorji <- c('grey', 'lightblue')
  colorji <- gg_color_hue(3)
  colorji <- colorji[c(1,3)]
  
  g <- ggplot(out)+
    geom_step(aes(time/365.241, prob, color=Curve), size=1.001
    )+
    scale_color_manual(values=colorji)+
    xlab(xlab_value)+
    ylab('Cumulative distribution function')
  
  
  
  poly_data <- plot.helper(yl, 'F_data')
  poly_P <- plot.helper(yl, 'F_P')
  
  g <- g+
    pammtools::geom_stepribbon(aes(x=time/365.241, ymin=0, ymax=prob, fill=Curve), alpha=0.3)+
    scale_fill_manual(values = colorji)
  
  if(!missing(xbreak)){
    g <- g +
      scale_x_continuous(expand = c(0, 0), limits=xlimits, breaks = xbreak)
  } else{
    g <- g +
      scale_x_continuous(expand = c(0, 0), limits=xlimits)
  }
  
  if(!missing(ybreak)){
    g <- g +
      scale_y_continuous(expand = c(0, 0), limits=ylimits, breaks = ybreak)
  } else{
    g <- g +
      scale_y_continuous(expand = c(0, 0), limits=ylimits)
  }
  
  g <- g +
    theme_bw()+
    # expand_limits(y = 0)+
    theme(legend.position = 'bottom',
          legend.title = element_blank())+
    theme(text = element_text(size=14))+
    theme(
      panel.grid.major.x = element_line(linetype='dashed', colour = 'grey85'),
      panel.grid.minor.x = element_line(linetype='dashed', colour = 'grey85'),
      panel.grid.major.y = element_line(linetype='dashed', colour = 'grey85'),
      panel.grid.minor.y = element_line(linetype='dashed', colour = 'grey85'))
  
  if(!show.legend){
    g <- g + 
      theme(legend.position = 'none') 
  }
  
  g
}

plot.yl.gg <- function(yl, xbreak, ybreak, xlimits, ylimits, yreverse=FALSE, conf.int=TRUE, ylabv, reverse=FALSE, ...){
  # yl: object given from the yl() function
  
  library(ggplot2)
  
  if(yl$starting.time == "left.truncated") xlab_value <- "Age"
  else xlab_value <- "Time since entry"
  
  if(yl$pop.curve == 'F_P'){
    ylab_value <- 'Years difference'
  } else if(yl$pop.curve == 'F_P_final'){
    ylab_value <- 'Years difference'
  } else{
    stop('Define ylab_value.')
  }
  if(!missing(ylabv)){
    ylab_value <- ylabv
  }
  
  
  out <- yl$yd_curve
  out$lower <- out$yd - (out$obs_var)^(1/2)*qnorm(0.975)
  out$upper <- out$yd + (out$obs_var)^(1/2)*qnorm(0.975)
  
  
  if(reverse){
    out$yd <- -out$yd
    tmp_lower <- out$lower
    out$lower <- -out$upper
    out$upper <- -tmp_lower
  }
  
  
  if(missing(xlimits)){
    xlimits <- c(min(yl$yd_curve$time[1]), max(yl$yd_curve$time))/365.241
  }
  if(missing(ylimits)){
    tmp_vec <- c(out$yd, out$lower, out$upper)
    ymax <- max(abs(tmp_vec))
    if(ymax %in% -tmp_vec) ymax = -ymax
    
    ylimits <- sort(c(0,ymax)*1.1)
    
  }
  
  g <- ggplot(out)+
    geom_step(aes(time/365.241, yd), size=1.001)
  
  if(conf.int){
    g <- g+
      geom_step(aes(time/365.241, lower))+
      geom_step(aes(time/365.241, upper))
  }
  
  g <- g+
    xlab(xlab_value)+
    ylab(ylab_value)
  
  if(!missing(xbreak)){
    g <- g+
      scale_x_continuous(expand = c(0, 0), limits=xlimits, breaks = xbreak)
  } else{
    g <- g+
      scale_x_continuous(expand = c(0, 0), limits=xlimits)
  }
  
  # Helper:
  trans <- function(x) -x
  inv <- function(x) -x
  reverse_fun <- scales::trans_new(name = "reverse_new",
                                   transform = trans,
                                   inverse = inv
  )
  ###
  
  if(!missing(ybreak)){
    g <- g +
      scale_y_continuous(expand = c(0, 0), limits = ylimits, breaks = ybreak)    
  } else{
    g <- g +
      scale_y_continuous(expand = c(0, 0), limits = ylimits)
  }
  if(yreverse){
    g <- g +
      coord_trans(y=reverse_fun)
  } 
  
  
  g <- g +
    theme_bw()+
    theme(text = element_text(size=14))+
    expand_limits(y = 0)+
    theme(
      panel.grid.major.x = element_line(linetype='dashed', colour = 'grey85'),
      panel.grid.minor.x = element_line(linetype='dashed', colour = 'grey85'),
      panel.grid.major.y = element_line(linetype='dashed', colour = 'grey85'),
      panel.grid.minor.y = element_line(linetype='dashed', colour = 'grey85'))
  
  g
}

