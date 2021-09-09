library(survival)
library(relsurv)
library(latex2exp)

# Helper function:
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
  # templab <- attr(rform$Terms, "term.labels")
  # if (!is.null(attr(rform$Terms, "specials")$ratetable)) 
  #   templab <- templab[-length(templab)]
  # nameslist <- vector("list", length(templab))
  # for (it in 1:length(nameslist)) {
  #   valuetab <- table(data[, match(templab[it], names(data))])
  #   nameslist[[it]] <- paste(templab[it], names(valuetab), 
  #                            sep = "")
  # }
  # names(nameslist) <- templab
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
    
    # Find true Yi:
    # true_yi <- temp$yi
    # 
    # if(include.censoring & (data$Y[inx] != tail(tis,1)) & (data$stat==0) ){
    #   true_yi[(data$Y[inx]+1):length(tis)] <- 0
    # }
    
    # # Probability of pop. survival until time of entry:
    # s_pi_t0 <- relsurv:::exp.prep(rform$R[inx, , drop = FALSE], rform$Y, rform$ratetable, 
    #                            rform$status, times = data$start[inx], fast = TRUE, cmp=FALSE,ys=0)
    # s_pi <- s_pi/exp(-s_pi_t0$yidli)
    
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

# Copied function from mstate:::NAfix.
mstateNAfix <- function (x, subst = -Inf) 
{
  spec <- max(x[!is.na(x)]) + 1
  x <- c(spec, x)
  while (any(is.na(x))) x[is.na(x)] <- x[(1:length(x))[is.na(x)] - 
                                           1]
  x[x == spec] <- subst
  x <- x[-1]
  x
}

# Main function: 

# A function that takes a dataset and returns the 
# cum. inc. function on the data, the population ones and the LYD
years <- function(formula=formula(data),
               data, 
               measure=c('yd', 'yl2017', 'yl2013'),
               estimator=c("F_P_final", "F_P_Spi", "F_P_Spi2", "F_P", "F_P2", "all"),
               ratetable=relsurv::slopop, 
               rmap,
               bootstrap=TRUE,
               B=10,
               precision=30, 
               add.times,
               na.action=na.omit,
               conf.int=0.95,
               timefix=FALSE,
               exact.hazards=FALSE,
               admin.cens,
               find.cond.time=FALSE,
               lt.point, 
               arg.example=FALSE,
               cause.val,
               is.boot=FALSE,
               first.boot=FALSE
){
  # formula: formula
  # data: dataset
  # ratetable: mortality tables
  # exact.hazards: calculate hazards on a daily basis (to be checked)
  # find.cond.time: if TRUE, return time at which there are at least 5 individuals in the at-risk set.
  # lt.point: fit the models conditional on time lt.point.
  # estimator: which estimator should be used for calculating the pop. cum. incidence curve
  # precision: the maximum number of days at which the population curve is evaluated. If time between events is bigger than precision, an in-between point is added at which the pop. curve is evaluated.
  # admin.cens: if not defined, administrative censoring is not taken into account. If a Date is supplied administrative censoring is taken until that time. Works only if starting.time=="left.truncated".
  # arg.example: temporary argument, used for checking additionalities
  # timefix: define timefix in survfit (for calculating the observed curve). Default is TRUE.
  
  # F_P_Spi: Tako kot F_P_final, ignorira censoring. Ali pa vzame samo admin cens
  # F_P_Spi2: Vzame ves censoring
  
  
  Call <- match.call()
  
  if(!missing(rmap) & !is.boot & !first.boot)  rmap <- substitute(rmap)
  
  estimator <- match.arg(estimator)
  measure <- match.arg(measure)
  
  data_orig <- data
  out <- NULL
  late.values <- FALSE
  
  
  # if(!missing(cause.val)){
  #   data$status <- ifelse(data$cause == cause.val, 1, 0)
  #   # Remove NAs:
  #   eniNAs <- which(is.na(data$status))
  #   if(length(eniNAs)>0) data <- data[-eniNAs,]
  # }
  
  # data$age <- round(data$age*365.241)
  # data$stop <- round(data$stop*365.241)
  
  # if(starting.time=="left.truncated"){
  if(!missing(admin.cens)){
    if(class(admin.cens)!='Date') warning('Object of class Date should be supplied to admin.cens.')
    end_date <- data$year+(data$stop-data$age)
    if(any(end_date > admin.cens)) warning('There are events that occur after the date of administrative censoring. Please check the values in arguments data and admin.cens.')
    id_admin_cens <- which(admin.cens==end_date)
  }
  # }
  
  starting_age <- rep(0,nrow(data))
  
  # If Surv(start,stop, event) (possibly + mstate)
  if_start_stop <- length(as.character(formula[[2]])) %in% c(4,5)
  
  if(if_start_stop){
    starting.time <- 'left.truncated'
  } else{
    starting.time <- 'zero'
  }
  
  if(if_start_stop){
    start_col <- as.character(formula[[2]])[2]
    stop_col <- as.character(formula[[2]])[3]
    starting_age <- data[, start_col]
  } else{
    stop_col <- as.character(formula[[2]])[2]
    if(!(stop_col %in% colnames(data))){
      stop(paste0('Instead of \'', stop_col, '\', please use a column from the data in the formula.'))
    }
  }
  
  starting_age <- as.numeric(starting_age)
  
  # # Take into account tau in time to event:
  # data$stop_tau <- round(data$age + tau*365.241)
  # # If tau before time to event:
  # wh <- which(data$stop_tau < data$stop)
  # data$stop[wh] <- data$stop_tau[wh]
  # data$status[wh] <- 0
  # # If tau after time to event, we have couple of options:
  # if(tau.par == "ignore"){
  #   # Ignore tau; use same time and status values
  # }
  # else if(tau.par == "extrapolate"){
  #   # Extrapolate and censor at stop_tau
  #   wh2 <- which(data$stop_tau > data$stop)
  #   data$stop[wh2] <- data$stop_tau[wh2]
  #   data$status[wh2] <- 0
  # }
  # else if(tau.par == "extrapolate2"){
  #   # Extrapolate and use the same status ind.
  #   wh2 <- which(data$stop_tau > data$stop)
  #   data$stop[wh2] <- data$stop_tau[wh2]
  # }
  # else  stop("tau.par doesn't match possible argument values c('ignore', 'extrapolate', 'extrapolate2').")
  # 
  # tau <- round(tau*365.241)
  # tau <- tau+data$age[1]
  
  # CIF on data:
  
  # if(any(data$age>=data$stop)) browser()
  surv_obj <- as.character(formula[[2]])
  
  if(missing(formula)){
    stop('Missing formula argument value.')
  } else{
    if('mstate' %in% surv_obj){
      juh <- 1:nrow(data)
      mod <- survival::survfit.formula(as.formula(Reduce(paste, deparse(formula))), data=data, timefix=timefix, id = juh, na.action=na.action)
    } else{
      mod <- survival::survfit.formula(formula, data=data, timefix=timefix, na.action=na.action)
    }
  }
  
  if('mstate' %in% surv_obj){
    surv_obj_new <- paste0(surv_obj[1], '(', surv_obj[2], ',', surv_obj[3])
    if(length(surv_obj)==5){
      surv_obj_new <- paste0(surv_obj_new, ',', surv_obj[4], ')')
    } else{
      surv_obj_new <- paste0(surv_obj_new, ')')
    }
    formula <- paste0(surv_obj_new, '~1')
  }
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
  # mod <- survfit(Surv(age, stop, status)~1, data=data_example)
  # plot(mod$time/365.241, 1-mod$surv, type="l") # CIF check 
  
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
    auc_data_vec <- cumsum(diff(c(0, mod$time))*(1 - survs))
  } else{
    auc_data <- mod$time*mod$surv
    auc_data_vec <- auc_data
  }
  
  out$F_data <- 1-mod$surv
  out$auc_data <- auc_data/365.241
  out$auc_data_vec <- auc_data_vec/365.241
  
  # HM???
  if(exact.hazards){
    mod$time <- seq(min(mod$time), max(mod$time), by=1)
    mod$surv <- exp(-cumsum(rep(ratetable[1,1,1], max(mod$time)-min(mod$time)+1)))
    
    out$F_data <- 1-exp(-cumsum(c(0, rep(ratetable[1,1,1], max(mod$time)-min(mod$time)))))
    out$auc_data <- sum(out$F_data)/365.241
  }
  
  ###
  if(measure %in% c('yl2017', 'yl2013')){
    # YL_P preparation:
    data_yi <- data
    rform <- relsurv:::rformulate(formula, data, ratetable, na.action=na.action, rmap = rmap)
    data <- rform$data
    if(if_start_stop){
      if(!(start_col %in% colnames(data))){
        data[,start_col] <- data_orig[, start_col]
      }
    }  
    
    # Check covariates:
    p <- rform$m
    if (p > 0) stop("There shouldn't be any covariates in the formula. This function gives non-parametric estimates of the hazards.")
    else data$Xs <- rep(1, nrow(data)) #if no covariates, just put 1
    
    out_n <- table(data$Xs) #table of strata
    out$time <- out$haz.excess <- out$haz.pop <- out$std.err <- out$strata <-  NULL
    
    kt <- 1 # the only stratum
    inx <- which(data$Xs == names(out_n)[kt]) #individuals within this stratum
    # tis <- sort(unique(rform$Y[inx])) #unique times
    if(!if_start_stop){
      tis <- rform$Y[inx] #unique times
      tis_seq <- seq(1, max(rform$Y[inx]), precision)
    } else{
      tis <- sort(unique(c(rform$Y[inx], data[, start_col]))) #unique times
      tis_seq <- seq(min(data[, start_col]), max(rform$Y[inx], data[, start_col]), precision)
    } 
    
    if(!is.boot){
      tis <- sort(unique(c(tis, tis_seq)))
    }
        
    if(!missing(add.times)){
      tis <- sort(unique(c(tis, add.times)))
    }
    ltis <- length(tis)
    
    # Fix demographic covariates:
    if(if_start_stop){
      rform$R[,"year"] <- rform$R[,"year"] - rform$R[,"age"]
      rform$R[,"age"] <- 0
    }
    
    if(measure == 'yl2017'){
      # YL_O (used only for yl2017):
      if(if_start_stop){
        it_auc <- rep(NA, nrow(data_orig))
        mod_sum <- summary(mod, times=unique(sort(c(data_orig[,start_col], data_orig[,stop_col]))))
        lsurv <- length(mod_sum$surv)
        val_mat <- matrix(0, nrow=nrow(data_orig), ncol=lsurv)
        for(it in 1:nrow(data_orig)){
          it_wh <- which(data_orig[it, start_col] == mod_sum$time)
          it_surv <- mod_sum$surv[it_wh:lsurv]/mod_sum$surv[it_wh]
          it_auc[it] <- sum(c(0, diff(mod_sum$time[it_wh:lsurv]))*(1 - it_surv))/365.241
          val_mat[it, it_wh:lsurv] <- cumsum(c(0, diff(mod_sum$time[it_wh:lsurv]))*(1 - it_surv))/365.241
        }
        YL_O_vec <- colMeans(val_mat)
        YL_O <- mean(it_auc)
        F_O_time <- mod_sum$time
      } else{
        YL_O_vec <- out$auc_data_vec
        YL_O <- out$auc_data
        F_O_time <- mod$time
      } 

      F_O <- data.frame(time=F_O_time, area=YL_O_vec)
      
      
      ###
      # YL_P continue:
      it_auc_P <- rep(NA, nrow(data))
      it_auc_P_mat <- matrix(0, nrow=nrow(data), ncol=ltis)
      
      for(it in 1:nrow(data)){
        temp <- relsurv:::exp.prep(rform$R[it,,drop=FALSE],max(rform$Y),rform$ratetable,rform$status[it],times=tis,fast=FALSE, cmp=FALSE, ys=starting_age[it], netweiDM = FALSE)
        # temp <- relsurv:::exp.prep(rform$R[inx,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status[inx],times=tis2,fast=FALSE, cmp=FALSE, ys=starting_age, netweiDM = TRUE)
        if(if_start_stop){
          it_wh <- which(data[it, start_col] == tis)
          hazs <- temp$yidli[it_wh:ltis]
          hazs[1] <- 0
          cumhazs <- cumsum(hazs)
          F_P <- 1 - exp(-cumhazs)
          it_auc_P[it] <- sum(c(tis[it_wh], diff(tis[it_wh:ltis]))*c(0, F_P[1:(length(F_P)-1)]))/365.241
          it_auc_P_mat[it,it_wh:ltis] <- sum(c(tis[it_wh], diff(tis[it_wh:ltis]))*c(0, F_P[1:(length(F_P)-1)]))/365.241
        } else{
          # it_wh <- which(data$age[it] == tis)
          hazs <- temp$yidli[1:ltis]
          hazs[1] <- 0
          cumhazs <- cumsum(hazs)
          F_P <- 1 - exp(-cumhazs)
          it_auc_P[it] <- sum(c(0, diff(tis))*c(0, F_P[1:(length(F_P)-1)]))/365.241
          it_auc_P_mat[it,] <- cumsum(c(0, diff(tis))*c(0, F_P[1:(length(F_P)-1)]))/365.241
        }
        
      }
      YL_P <- mean(it_auc_P)
      YL=YL_O-YL_P
      F_P <- data.frame(time=tis, area=colMeans(it_auc_P_mat))
    
      F_O_tajms <- F_P$time[!(F_P$time %in% F_O$time)]
      if(length(F_O_tajms)>0){
        F_O_tmp <- data.frame(time=F_O_tajms, area=NA)
        F_O_ext <- rbind(F_O, F_O_tmp)
        F_O_ext <- F_O_ext[order(F_O_ext$time),]
        F_O_ext$area <- mstateNAfix(F_O_ext$area, 0)
        yd_curve <- data.frame(time=tis, est=F_O_ext$area - F_P$area)
      } else{
        yd_curve <- data.frame(time=tis, est=F_O$area - F_P$area)
      }
      
      # Bootstrap:
      if(bootstrap){
        data_b <- data_orig
        data_b$id <- 1:nrow(data_b)
        yl_boot <- ylboot(theta=ylboot.iter, data=data_b, id="id",
                          B=B, verbose=0, #all_times = all_times,
                          ratetable=ratetable#, add.times=add.times
                          , starting.time, estimator, precision,
                          add.times = add.times,
                          formula = formula,
                          rmap = rmap, measure=measure
        )
        if(ncol(yl_boot[[2]])>nrow(F_O)){
          varsincol <- colVars(yl_boot[[2]], na.rm=TRUE)^(1/2)
          varsincol_df <- data.frame(time=yl_boot[[4]], area.se=varsincol)
          varsincol_df <- varsincol_df[varsincol_df$time %in% F_O$time,]
          F_O$area.se <- varsincol_df$area.se
        } else{
          F_O$area.se <- colVars(yl_boot[[2]], na.rm=TRUE)^(1/2)
        }
        F_P$area.se <- colVars(yl_boot[[3]], na.rm=TRUE)^(1/2)
        yl_boot <- as.data.frame(t(yl_boot[[1]]))
        yd_curve$est.se <- (colVars(yl_boot, na.rm=TRUE))^(1/2)
        
      }
      
      return(list(years=yd_curve, F_O=F_O, F_P=F_P, measure=measure))
      
    } else{
      temp <- relsurv:::exp.prep(rform$R[,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status,times=tis, fast=TRUE, cmp=FALSE, ys=starting_age)
      # temp <- relsurv:::exp.prep(rform$R[,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status,times=mod$time, fast=TRUE, cmp=FALSE, ys=starting_age)
      
      temp$yi[temp$yi==0] <- Inf
      
      out$time <- c(out$time, tis)						#add times
      # out$time <- c(out$time, mod$time)						#add times
      
      # out$n.risk <- c(out$n.risk, temp$yi)					#add number at risk for each time
      # out$n.event <- c(out$n.event, temp$dni)					#add number of events for each time
      # out$n.censor <- c(out$n.censor,  c(-diff(temp$yi),temp$yi[length(temp$yi)]) - temp$dni) 	#add number of censored for each time
      
      # Calculate hazards:
      haz.pop <- temp$yidli/temp$yi
      
      out$haz.pop <- c(out$haz.pop,haz.pop)
      out$cum.haz.pop <- cumsum(out$haz.pop)
      
      mod_tis <- summary(mod, times = tis)
      # mod_tis <- summary(mod, times = mod$time)
      F_E <- cumsum(mod_tis$surv*(mod_tis$n.event/mod_tis$n.risk - haz.pop))
      ltis <- length(tis)
      # browser()      
      # Var as in Pavlic2018:
      F_E_st <- sapply(1:ltis, function(s){
        sum(mod_tis$surv[s:ltis]/mod_tis$surv[s]*(mod_tis$n.event[s:ltis]/mod_tis$n.risk[s:ltis] - haz.pop[s:ltis])*c(0, diff(tis[s:ltis]))/365.241)
      })
      F_Ese <- (cumsum((mod_tis$surv)^2*(1 - F_E_st)^2*(mod_tis$n.event/mod_tis$n.risk^2)*c(0, diff(tis))/365.241))^(1/2)
      
      
      YL <- cumsum(F_E*c(0, diff(tis))/365.241)
      
      F_E_df <- data.frame(time=tis, prob=F_E, prob.se=F_Ese)
      yd_curve <- data.frame(time=tis, est=YL)
      
      if(bootstrap){
        data_b <- data_orig
        data_b$id <- 1:nrow(data_b)
        yl_boot <- ylboot(theta=ylboot.iter, data=data_b, id="id",
                          B=B, verbose=0, #all_times = all_times,
                          ratetable=ratetable#, add.times=add.times
                          , starting.time, estimator, precision,
                          add.times = add.times,
                          formula = formula,
                          rmap = rmap, measure=measure
        )
        F_E_df$prob.se <- (colVars(yl_boot[[2]], na.rm=TRUE))^(1/2)
        yl_boot <- as.data.frame(t(yl_boot[[1]]))
        yd_curve$est.se <- (colVars(yl_boot, na.rm=TRUE))^(1/2)
        
      }
      
      out <- list(years=yd_curve, F_E=F_E_df, measure=measure)
      
      return(out)
    }
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
  # obs_var_time <- cumsum(((auc_all[length(auc_all)] - auc_all)^2*mod$n.event)/(mod$n.risk*(mod$n.risk - mod$n.event)))
  
  # # RMST code:
  # tau <- mod$time[length(mod$time)]/365.241
  # idx = (mod$time/365.241) <= tau
  # wk.time = sort(c(mod$time[idx]/365.241, tau))
  # wk.surv = mod$surv[idx]
  # wk.n.risk = mod$n.risk[idx]
  # wk.n.event = mod$n.event[idx]
  # time.diff <- diff(c(0, wk.time))
  # areas <- time.diff * c(1, wk.surv)
  # rmst = sum(areas)
  # # rmst
  # wk.var <- ifelse((wk.n.risk - wk.n.event) == 0, 0, wk.n.event/(wk.n.risk * (wk.n.risk - wk.n.event)))
  # wk.var = c(wk.var, 0)
  # rmst.var = sum(cumsum(rev(areas[-1]))^2 * rev(wk.var)[-1])
  # 
  # help_fun <- function(tau){
  #   # tau <- mod$time[length(mod$time)]/365.241
  #   idx = (mod$time/365.241) <= tau
  #   wk.time = sort(c(mod$time[idx]/365.241, tau))
  #   wk.surv = mod$surv[idx]
  #   wk.n.risk = mod$n.risk[idx]
  #   wk.n.event = mod$n.event[idx]
  #   time.diff <- diff(c(0, wk.time))
  #   areas <- time.diff * c(1, wk.surv)
  #   rmst = sum(areas)
  #   # rmst
  #   wk.var <- ifelse((wk.n.risk - wk.n.event) == 0, 0, wk.n.event/(wk.n.risk * 
  #                                                                    (wk.n.risk - wk.n.event)))
  #   wk.var = c(wk.var, 0)
  #   rmst.var = sum(cumsum(rev(areas[-1]))^2 * rev(wk.var)[-1])
  #   rmst.var
  # }
  # obs_var_time22 <- sapply(mod$time/365.241, help_fun)

  ################################################### #
  
  # CIF on population:
  
  # Take into account conditional probabilities in the data:
  if(!missing(lt.point)){
    data <- subset(data, stop>lt.point)
    data[, start_col] <- ifelse(data[, start_col]<lt.point, lt.point, data[, start_col])
    starting_age <- data[, start_col]
    starting_age <- as.numeric(starting_age)
  }
  
  data_yi <- data
  # if(any(data[, start_col]>=data[, stop_col])) browser()
  
  # if(!missing(cause.val)){
  #   # data[,'status'] <- NA
  #   # data[,'status'] <- ifelse(data[,status_obj]==cause.val, 1, 0)
  #   data[,status_obj] <- ifelse(data[,status_obj]==cause.val, 1, 0)
  # }
  
  # rform <- relsurv:::rformulate(as.formula(formula), data, ratetable, na.action=na.omit)
  # browser()
  rform <- relsurv:::rformulate(formula, data, ratetable, na.action=na.action, rmap = rmap)
  data <- rform$data
  if(if_start_stop){
    if(!(start_col %in% colnames(data))){
      data[,start_col] <- data_orig[, start_col]
    }
  }
  
  # Check covariates:
  p <- rform$m
  if (p > 0) stop("There shouldn't be any covariates in the formula. This function gives non-parametric estimates of the hazards.")
  else data$Xs <- rep(1, nrow(data)) #if no covariates, just put 1
  
  out_n <- table(data$Xs) #table of strata
  out$time <- out$haz.excess <- out$haz.pop <- out$std.err <- out$strata <-  NULL
  
  kt <- 1 # the only stratum
  inx <- which(data$Xs == names(out_n)[kt]) #individuals within this stratum
  # tis <- sort(unique(rform$Y[inx])) #unique times
  if(!if_start_stop) tis <- sort(unique(c(rform$Y[inx], seq(1, max(rform$Y[inx]), precision)))) #unique times
  else tis <- sort(unique(c(rform$Y[inx], data[, start_col], seq(min(data[, start_col]), max(rform$Y[inx], data[, start_col]), precision)))) #unique times
  # Added 2 monthly times between entries and event times
  
  if(!missing(add.times)){
    tis <- sort(unique(c(tis, add.times)))
  }
  
  # if(tau %in% tis) tis <- tis[tis<=tau]
  # else if(tau < tail(tis, 1)) tis <- c(tis[tis<tau], tau)
  # else warning("Argument tau is bigger than the maximum time in the data. Values will be calculated until maximum time.")
  
  # Fix demographic covariates:
  if(if_start_stop){
    rform$R[,"year"] <- rform$R[,"year"] - rform$R[,"age"]
    rform$R[,"age"] <- 0
  }
  
  if(estimator=='F_P' | estimator=="all"){
    # Prepare at-risk matrix:
    # browser()
    # mat <- lapply(1:nrow(data), function(x) ifelse((data$start[x] < tis) & (tis <= data$Y[x]), 1, NA))
    # mat2 <- matrix(unlist(mat), nrow = nrow(data_yi), byrow = TRUE)
    # # The sum of the individual at-risk processes:
    # yi_left <- colSums(mat2)
    # yi_left[yi_left == 0] <- Inf
    # 
    # mat3 <- lapply(1:nrow(data), function(x) data$age[x] + c(0, diff(tis)))
    
    if(any(rform$Y[inx]<=starting_age)) browser()
    # browser()
    # formula2 <- Surv(age,stop,status)~1
    # rform2 <- relsurv:::rformulate(formula2, data_orig, ratetable)
    temp <- relsurv:::exp.prep(rform$R[inx,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status[inx],times=tis,fast=TRUE, cmp=FALSE, ys=starting_age)
    # browser()
    # Fix at-risk process, if needed:
    temp$yi[temp$yi==0] <- Inf
    
    out$time <- c(out$time, tis)						#add times
    # out$n.risk <- c(out$n.risk, temp$yi)					#add number at risk for each time
    # out$n.event <- c(out$n.event, temp$dni)					#add number of events for each time
    # out$n.censor <- c(out$n.censor,  c(-diff(temp$yi),temp$yi[length(temp$yi)]) - temp$dni) 	#add number of censored for each time
    
    # Calculate hazards:
    haz.pop <- temp$yidli/temp$yi
    out$haz.pop <- c(out$haz.pop,haz.pop)
    out$cum.haz.pop <- cumsum(out$haz.pop)
    out$F_P <- 1-exp(-out$cum.haz.pop)
    out$auc_pop <- sum(c(tis[1], diff(tis))*c(0, out$F_P[1:(length(out$F_P)-1)]))/365.241
    
  } 
  data_spi2 <- data
  
  if(estimator=='F_P_Spi2' | estimator=="all"){
    
    if(any(data_spi2$start>=data_spi2$Y)) browser()
    # tis_juh <- seq(min(tis), max(tis), by=1)
    # Take into account censoring:
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
  if(estimator=='F_P_Spi' | estimator=="all"){
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
  
  if(estimator=='F_P_final'){
    # Shift all to the end:
    if(if_start_stop) data_yi[,stop_col] <- max(data_yi[,stop_col])
    
    rform2 <- rform
    # if(any(data_yi[, start_col]>=data_yi[, stop_col])) browser()
    
    rform <- relsurv:::rformulate(formula, data_yi, ratetable, na.action=na.action, rmap = rmap)
    
    # Shift all to the end:
    if(!if_start_stop){
      rform$Y <- rep(max(rform$Y), length(rform$Y))
      rform$data[,"Y"] <- rform$Y
    } 
    data <- rform$data    
    if(if_start_stop){
      if(!(start_col %in% colnames(data))){
        data[,start_col] <- data_orig[, start_col]
      }
    }
  
    # Check covariates:
    p <- rform$m
    if (p > 0) stop("There shouldn't be any covariates in the formula. This function gives non-parametric estimates of the hazards.")
    else data$Xs <- rep(1, nrow(data)) #if no covariates, just put 1
    
    out$haz.pop2 <- NULL
    
    kt <- 1 # the only stratum
    inx <- which(data$Xs == names(out_n)[kt]) #individuals within this stratum
    tis2 <- tis
    # tis2 <- c(0, tis2[1:(length(tis2)-1)])
    # tis2 <- sort(unique(rform$Y[inx])) #unique times
    
    # Fix demographic covariates:
    if(if_start_stop){
      rform$R[,"year"] <- rform$R[,"year"] - rform$R[,"age"]
      rform$R[,"age"] <- 0
    }
    
    if(any(starting_age>=rform$Y[inx])) browser()
    # temp <- relsurv:::exp.prep(rform$R[inx,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status[inx],times=tis2,fast=TRUE, cmp=FALSE, ys=0)	
    # temp <- relsurv:::exp.prep(rform$R[inx,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status[inx],times=tis2,fast=TRUE, cmp=FALSE, ys=starting_age)	
    temp <- relsurv:::exp.prep(rform$R[inx,,drop=FALSE],rform$Y[inx],rform$ratetable,rform$status[inx],times=tis2,fast=FALSE, cmp=FALSE, ys=starting_age, netweiDM = TRUE)
    # browser()
    # Calculate hazards:
    # if(starting.time=='left.truncated'){
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
  
  if(estimator=='F_P2' | estimator=="all"){
    # Shift all to the end:
    if(if_start_stop) data_yi[,stop_col] <- max(data_yi[,stop_col])
    
    rform2 <- rform
    # if(any(data_yi[, start_col]>=data_yi[, stop_col])) browser()
    
    rform <- relsurv:::rformulate(formula, data_yi, ratetable, na.action=na.action, rmap = rmap)
    
    # Shift all to the end:
    if(!if_start_stop){
      rform$Y <- rep(max(rform$Y), length(rform$Y))
      rform$data[,"Y"] <- rform$Y
    } 
    data <- rform$data    
    if(if_start_stop){
      if(!(start_col %in% colnames(data))){
        data[,start_col] <- data_orig[, start_col]
      }
    }
    
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
    if(if_start_stop){
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
                       ratetable=ratetable#, add.times=add.times
                       , starting.time, estimator, precision,
                      add.times = add.times,
                      formula = formula,
                      rmap = rmap, measure=measure
    )
    L_OP <- yl_boot[[3]]
    F_boot <- yl_boot[[2]]
    yl_boot <- as.data.frame(t(yl_boot[[1]]))
  }
  ###
  estimator.orig <- estimator
  if(estimator=='F_P_final') estimator = 'F_P2'
  
  out$strata <- c(out$strata, length(tis))				#number of times in this strata
  names(out$strata) <-  names(out_n)
  out$strata <-  NULL
  out$auc <- c(auc_data=out$auc_data, auc_pop=out$auc_pop, auc_pop2=out$auc_pop2, auc_pop_Spi=out$auc_pop_Spi, auc_pop_Spi2=out$auc_pop_Spi2)
  
  if(estimator=='all'){
    F_P_final <- data.frame(time=out$time,F_P=out$F_P, F_P2=out$F_P2, F_P_Spi=out$F_P_Spi, F_P_Spi2=out$F_P_Spi2)
  } else if(estimator=='F_P'){
    F_P_final <- data.frame(time=tis,prob=out$F_P)
  } else if(estimator=='F_P2'){
    F_P_final <- data.frame(time=tis,prob=out$F_P2)
  } else if(estimator=='F_P_Spi'){
    F_P_final <- data.frame(time=tis,prob=out$F_P_Spi)
  } else if(estimator=='F_P_Spi2'){
    F_P_final <- data.frame(time=tis,prob=out$F_P_Spi2)
  } 
  
  # YD through time:
  # if(is.boot) browser()
  
  F_data_yd <- data.frame(time=mod$time, F_data=out$F_data, var=obs_var_time)
  pop.times <- F_P_final$time[!(F_P_final$time %in% mod$time)]
  if(length(pop.times) > 0){
    F_data_yd_tmp <- data.frame(time=pop.times, F_data=NA, var=NA)
    F_data_yd <- rbind(F_data_yd, F_data_yd_tmp)
    F_data_yd <- F_data_yd[order(F_data_yd$time),]
    F_data_yd$F_data <- mstateNAfix(F_data_yd$F_data, 0)
    F_data_yd$var <- mstateNAfix(F_data_yd$var, 0)
  }
  
  yd_data <- cumsum(c(F_data_yd$time[1], diff(F_data_yd$time))*c(0, F_data_yd$F_data[1:(nrow(F_data_yd)-1)]))/365.241

  F_P_yd <- F_P_final
  yd_pop <- cumsum(c(F_P_yd$time[1], diff(F_P_yd$time))*c(0, F_P_yd$prob[1:(nrow(F_P_yd)-1)]))/365.241
  # yd_pop <- yd_pop[F_P_final$time %in% mod$time]
  yd_curve <- data.frame(time=F_data_yd$time, yd=yd_data - yd_pop, 
                         obs_var=F_data_yd$var,
                         # obs_var22=obs_var_time22,
                         yd_data=yd_data,
                         yd_pop=yd_pop
                         )
  ###
  # Add values at time zero:
  
  F_data_tmp <- data.frame(time=mod$time,
             prob=out$F_data,
             prob.se=mod$std.err,
             area=NA,
             area.se=NA)
  F_tmp <- F_data_tmp[1,]
  F_tmp$time <- min(starting_age)
  F_tmp$prob <- 0
  F_tmp$prob.se <- 0
  if(!(F_tmp$time %in% F_data_tmp$time)) F_data_tmp <- rbind(F_tmp, F_data_tmp)
  
  if(!if_start_stop){
    F_P_final_tmp <- F_P_final[1,]
    F_P_final_tmp$time <- min(starting_age)
    F_P_final_tmp$prob <- 0
    if(!(F_P_final_tmp$time %in% F_P_final$time)) F_P_final <- rbind(F_P_final_tmp, F_P_final)
  }
  
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
  
  # Final form:
  # if(bootstrap) browser()

  # Add areas:
  F_data_tmp$area <- yd_curve$yd_data[yd_curve$time %in% F_data_tmp$time]
  F_P_final$area <- yd_curve$yd_pop#[yd_curve$time %in% F_P_final$time]
  F_data_tmp$area.se <- yd_curve$obs_var[yd_curve$time %in% F_data_tmp$time]^(1/2)
  
  # If, add boot variance: 
  if(bootstrap & (!is.boot)){
    F_data_tmp$prob.se <- (F_boot$F_data[F_boot$time %in% F_data_tmp$time])^(1/2)
    F_P_final$prob.se <- (F_boot$F_P#[F_boot$time %in% F_P_final$time]
                          )^(1/2)
    F_data_tmp$area.se <- L_OP$L_O[L_OP$time %in% F_data_tmp$time]^(1/2)
    F_P_final$area.se <- L_OP$L_P^(1/2)
  } 

  # Column order:
  F_data_tmp <- F_data_tmp[, c('time', 'prob', 'area', 'prob.se', 'area.se')]
  
  # Choose relevant columns:
  if(bootstrap){
    yd_curve <- yd_curve[,c('time', 'yd', 'boot_var')]
  } else{
    yd_curve <- yd_curve[,c('time', 'yd', 'obs_var')]
  }
  yd_curve[,3] <- yd_curve[,3]^(1/2)
  colnames(yd_curve)[2:3] <- c('est', 'est.se')
  yd_curve$lower <- yd_curve$est - yd_curve$est.se*qnorm(0.5+conf.int/2)
  yd_curve$upper <- yd_curve$est + yd_curve$est.se*qnorm(0.5+conf.int/2)
  
  return_obj <- list(F_data=F_data_tmp,
                     F_P=F_P_final,
                     auc=out$auc,
                     yd_curve=yd_curve,
                     starting.time=starting.time,
                     estimator=estimator.orig,
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
  
  return_short <- list(years=return_obj$yd_curve, F_O=return_obj$F_data, F_P=return_obj$F_P, measure=measure)
  
  if((bootstrap & (!is.boot)) #| ((!bootstrap) & (!is.boot))
     ){
    return_obj <- return_short
  }
  if((!bootstrap) & (!is.boot)){
    return_obj <- return_short
  }
  
  return(return_obj)
}

# Bootstrap function:
ylboot <- function(theta, data, B = 5, id = "id", verbose = 0, 
                           #all_times, 
                   ratetable=relsurv::slopop, #add.times, 
                   starting.time, estimator, precision,
                   add.times,
                   formula,
                   rmap, measure,
                   ...){
  # if (!inherits(data, "msdata")) 
  #   stop("'data' must be a 'msdata' object")
  ids <- unique(data[, id])
  n <- length(ids)
  if(!missing(add.times)){
    th <- ylboot.iter(formula, data, starting.time = starting.time, estimator = estimator, precision = precision,
                      ratetable=ratetable, first=TRUE, add.times = add.times, rmap = rmap, measure=measure, ...)
  } else{
    th <- ylboot.iter(formula, data, starting.time = starting.time, estimator = estimator, precision = precision,
                      ratetable=ratetable, first=TRUE, rmap = rmap, measure=measure, ...)
  }
  
  simple_par <- TRUE
  if(missing(add.times)) simple_par <- FALSE
  
  # Prepare objects:
  res <- data.frame(matrix(NA, nrow=B, ncol=nrow(th[[1]])))
  if(!missing(add.times)){
    # add.times2 <- add.times
  } else{
    add.times <- th[[1]]$time
  }
  # else{
  #   if(starting.time=='left.truncated'){
  #     add.times2 <- max(data$stop)
  #   } else{
  #     add.times2 <- max(data$stop - data$age)
  #   } 
  # }
  
  Fdata <- data.frame(matrix(NA, nrow=B, ncol=length(add.times)))
  Fo <- data.frame(matrix(NA, nrow=B, ncol=nrow(th[[2]])))
  Fp <- data.frame(matrix(NA, nrow=B, ncol=length(add.times)))
  L_O <- data.frame(matrix(NA, nrow=B, ncol=length(add.times)))
  L_P <- data.frame(matrix(NA, nrow=B, ncol=length(add.times)))
  F_E <- data.frame(matrix(NA, nrow=B, ncol=length(add.times)))
  
  # Iteration:
  for (b in 1:B) {
    nek_obj <- ylboot.apply(formula, b, verbose, ids, data, id, add.times, starting.time, estimator, precision, ratetable, th, simple_par, rmap, measure, ...)
    res[b,1:length(nek_obj[[1]])] <- nek_obj[[1]]
    if(measure=='yl2013'){
      F_E[b,1:length(nek_obj[[2]])] <- nek_obj[[2]]
    }
    if(measure=='yl2017'){
      Fo[b,1:length(nek_obj[[2]])] <- nek_obj[[2]]
      Fp[b,1:length(nek_obj[[3]])] <- nek_obj[[3]]
    }
    if(measure=='yd'){
      subnek <- subset(nek_obj[[2]], time %in% add.times)
      
      sub_vec <- 1:nrow(subnek)
      Fdata[b,sub_vec] <- subnek$F_data
      Fp[b,sub_vec] <- subnek$F_P
      
      subnek2 <- subset(nek_obj[[3]], time %in% add.times)
      
      sub2_vec <- 1:nrow(subnek2)
      L_O[b,sub2_vec] <- subnek2$yd_data
      L_P[b,sub2_vec] <- subnek2$yd_pop
    }    
  }
  # res <- vapply(1:B, function(b) ylboot.apply(b, verbose, ids, data, id, add.times, starting.time, estimator, precision, ratetable, th, simple_par,
  #                                             ...),
  #        FUN.VALUE = rep(1, nrow(th[[2]])))
  res <- as.data.frame(t(res))
  
  if(measure == 'yl2013'){
    return(list(res, F_E))
  } 
  if(measure == 'yl2017'){
    return(list(res, Fo, Fp, add.times))
  }
  else{
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
}

ylboot.apply <- function(formula, b, verbose, ids, data, id, add.times, starting.time, estimator, precision, ratetable, th, simple_par,
                         rmap, measure,
                         ...){
  
  if(starting.time=='left.truncated'){
    start_col <- as.character(formula[[2]])[2]
    stop_col <- as.character(formula[[2]])[3]
  } else{
    stop_col <- as.character(formula[[2]])[2]
  }
  
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
    # print(date())
    # print(events(bootdata))
    cat("applying theta ...")
  }
  
  if(length(unique(bootdata[,id]))==1){
    next
  } 

  if(!missing(add.times) & simple_par){
    add.times.arg <- sort(unique(c(th[[1]]$time, add.times)))
  } else{
    add.times.arg <- th[[1]]$time
  }
  add.times.arg2 <- add.times.arg
  # Remove unnecessary times
  if(starting.time == 'left.truncated'){
    add.times.arg <- add.times.arg[add.times.arg<=max(bootdata[,stop_col])]
  } else{
    add.times.arg <- add.times.arg[add.times.arg<=max(bootdata[,stop_col])]# - bootdata[,start_col])]
  }
  
  thstar <- ylboot.iter(formula, bootdata, starting.time = starting.time, estimator = estimator, precision = precision,
                        ratetable=ratetable, add.times=add.times.arg, rmap=rmap, measure=measure, ...)
  if(measure == 'yl2013'){
    return(list(thstar[[1]]$est, thstar[[2]]$prob))
  } 
  if(measure == 'yl2017'){
    FoO <- thstar[[2]]
    FpP <- thstar[[3]]
    thstar <- thstar[[1]]
    # if(nrow(th[[1]]) != nrow(thstar)) browser()
    
    if(nrow(FoO) < nrow(th[[2]])){
      mis.tajms <- th[[2]]$time[!(th[[2]]$time %in% FoO$time)]
      mis.tajms <- mis.tajms[mis.tajms <= max(FoO$time)]
      temp_df <- data.frame(time=mis.tajms, area=NA)
      FoO <- rbind(FoO, temp_df)
      FoO <- FoO[order(FoO$time),]
      FoO$area <- mstateNAfix(FoO$area, 0)  
    }
    
    if(nrow(th[[1]]) < nrow(thstar)){
      browser()
      thstar <- thstar[thstar$time %in% th[[1]]$time, ]
      FpP <- FpP[FpP$time %in% th[[1]]$time, ]
      foO <- foO[foO$time %in% th[[1]]$time, ]
    }
    
    if(length(th[[1]]$time[th[[1]]$time <= max(thstar$time)]) != length(thstar$time)) browser()
    pogoj <- any(th[[1]]$time[th[[1]]$time <= max(thstar$time)] != thstar$time)
    if(pogoj){
      browser()
      missing_times <- th[[1]]$time[which(!(th[[1]]$time %in% thstar$time))]
      
      if(length(missing_times)>0){
        # There are times missing in thstar, add them:
        add_df <- thstar[1:length(missing_times),]
        add_df$time <- missing_times
        add_df$yd <- NA
        add_df$obs_var <- NA
        add_df$yd_data <- NA
        
        thstar <- rbind(thstar, add_df)
        thstar <- thstar[order(thstar$time),] # redundantno
        
        thstar$yd <- mstateNAfix(thstar$yd, 0)
        thstar$obs_var <- mstateNAfix(thstar$obs_var, 0)
        thstar$yd_data <- mstateNAfix(thstar$yd_data, 0)
        
        if(nrow(th[[1]]) < nrow(thstar)){
          thstar <- thstar[thstar$time %in% th[[1]]$time, ]
        }
        
        if(nrow(th[[1]]) != nrow(thstar)) browser()      
      } else{ 
        # This means there's more times in thstar than needed. Remove unnecessary times:
        thstar <- thstar[-which(!(thstar$time %in% th[[1]]$time)),]
        FpP <- FpP[-which(!(FpP$time %in% th[[1]]$time)),]
        foO <- foO[-which(!(foO$time %in% th[[1]]$time)),]
        
        if(nrow(th[[1]]) != nrow(thstar)) browser()
      } 
    }
    
    return(list(thstar$est, FoO$area, FpP$area))
  } 
  
  L_OP <- thstar[[3]]
  Fobj <- thstar[[2]]
  thstar <- thstar[[1]]
  
  if(nrow(th[[1]]) < nrow(thstar)){
    thstar <- thstar[thstar$time %in% th[[1]]$time, ]
    L_OP <- L_OP[L_OP$time %in% th[[1]]$time, ]
    Fobj <- Fobj[Fobj$time %in% th[[1]]$time, ]
  }
  
  # Ali kaksne vrednosti manjkajo:
  if(length(th[[1]]$time[th[[1]]$time <= max(thstar$time)]) != length(thstar$time)) browser()
  pogoj <- any(th[[1]]$time[th[[1]]$time <= max(thstar$time)] != thstar$time)
  if(pogoj){
    
    missing_times <- th[[1]]$time[which(!(th[[1]]$time %in% thstar$time))]
    
    if(length(missing_times)>0){
      # There are times missing in thstar, add them:
      add_df <- thstar[1:length(missing_times),]
      add_df$time <- missing_times
      add_df$yd <- NA
      add_df$obs_var <- NA
      add_df$yd_data <- NA
      
      thstar <- rbind(thstar, add_df)
      thstar <- thstar[order(thstar$time),] # redundantno
      
      thstar$yd <- mstateNAfix(thstar$yd, 0)
      thstar$obs_var <- mstateNAfix(thstar$obs_var, 0)
      thstar$yd_data <- mstateNAfix(thstar$yd_data, 0)
      
      if(nrow(th[[1]]) < nrow(thstar)){
        thstar <- thstar[thstar$time %in% th[[1]]$time, ]
      }
      
      if(nrow(th[[1]]) != nrow(thstar)) browser()      
    } else{ 
      # This means there's more times in thstar than needed. Remove unnecessary times:
      thstar <- thstar[-which(!(thstar$time %in% th[[1]]$time)),]
      L_OP <- L_OP[-which(!(L_OP$time %in% th[[1]]$time)),]
      Fobj <- Fobj[-which(!(Fobj$time %in% th[[1]]$time)),]
      
      if(nrow(th[[1]]) != nrow(thstar)) browser()
    } 
  }
  
  # thstar$b <- b
  # Save result: 
  # res[b,] <- 

  list(thstar$est, Fobj, L_OP)
}

ylboot.iter <- function(formula, data, #all_times,
                        starting.time, estimator, precision,
                        ratetable=relsurv::slopop,
                        first=FALSE, add.times,
                        rmap, measure
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
    object <- years(formula = formula, data = data, ratetable = ratetable, 
                 estimator = estimator, precision=precision, bootstrap=FALSE, is.boot=is.boot, first.boot = first.boot, rmap = rmap, measure=measure)
  } else{
    object <- years(formula = formula, data = data, ratetable = ratetable, 
                 estimator = estimator, precision=precision, bootstrap=FALSE, add.times=add.times, is.boot=is.boot, first.boot = first.boot, rmap = rmap, measure=measure)
  }
  if(measure=='yd'){
    if(first) return(list(object$yd_curve, object$F_data))
    else{
      # return(object$yd_curve)
      Fobj <- merge(object$F_P[,c('time','prob')], object$F_data[,c('time','prob')], by='time', all.x=TRUE)
      Fobj <- Fobj[,c(1,3,2)]
      colnames(Fobj)[2:3] <- c('F_data','F_P')
      
      L_OP <- merge(object$F_P[,c('time','area')], object$F_data[,c('time','area')], by='time', all.x = TRUE)
      L_OP <- L_OP[,c(1,3,2)]
      colnames(L_OP)[2:3] <- c('yd_data', 'yd_pop')
      
      return(list(object$yd_curve,
                  Fobj,
                  L_OP))
    }
  } else if(measure=='yl2013'){
    return(list(object$years, object$F_E))
  } else{
    return(list(object$years, object$F_O, object$F_P))
  }
   
}

plot.helper <- function(years, obj){
  
  df_poly <- data.frame(time=years[[obj]]$time/365.241,
                        prob=years[[obj]]$prob)
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

plot.f <- function(years, xlab='Time interval', ylab='Absolute risk', xbreak, ybreak, xlimits, ylimits, show.legend=TRUE, ...){
  # years: object given from the years() function
  # xlab: define xlab 
  # ylab: define ylab 
  # xbreak: The breaks on x axis
  # ybreak: The breaks on y axis
  # xlimits: Define the limits on the x axis
  # ylimits: Define the limits on the y axis
  # show.legend: TRUE by default (shows the legend)

  library(ggplot2)
  
  if(years$measre != 'yd'){
    stop("The plot.f function is only available for the life years difference measure (argument measure='yd' in the years function).")
  }
  
  out <- rbind(
    cbind(years$F_O, Curve='Observed'),
    cbind(years$F_P, Curve='Population')
  )
  
  if(missing(xlimits)){
    xlimits <- c(min(out$time), max(out$time))/365.241
  }
  if(missing(ylimits)){
    ylimits <- c(0,max(out$prob))*1.1
  }
  
  colorji <- gg_color_hue(3)
  colorji <- colorji[c(1,3)]
  
  g <- ggplot(out)+
      geom_step(aes(time/365.241, prob, color=Curve), size=1.001
                )+
    scale_color_manual(values=colorji)+
    xlab(xlab)+
    ylab(ylab)
  
  poly_data <- plot.helper(years, 'F_O')
  poly_P <- plot.helper(years, 'F_P')

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

plot.years <- function(years, xlab='Time interval', ylab='Years', xbreak, ybreak, xlimits, ylimits, conf.int=TRUE, ymirror=FALSE, yminus=FALSE, ...){
  # years: the object obtained from the years function
  # xlab: define xlab 
  # ylab: define ylab 
  # xbreak: The breaks on x axis
  # ybreak: The breaks on y axis
  # xlimits: Define the limits on the x axis
  # ylimits: Define the limits on the y axis
  # conf.int: plot confidence intervals
  # ymirror: Mirror the y values on the figure
  # yminus: Use function y -> -y when plotting
  
  
  library(ggplot2)
  
  out <- years$years
  
  if(conf.int){
    if(is.null(out$lower)){
      stop('Confidence intervals not present in the years object. Please use the bootstrap argument in the years function.')
    }
  }

  if(yminus){
    out$est <- -out$est
    tmp_lower <- out$lower
    out$lower <- -out$upper
    out$upper <- -tmp_lower
  }
  
  if(missing(xlimits)){
    xlimits <- c(min(years$years$time[1]), max(years$years$time))/365.241
  }
  if(missing(ylimits)){
    tmp_vec <- c(out$est, out$lower, out$upper)
    ymax <- max(tmp_vec)
    ymin <- min(tmp_vec)
    ylimits <- c(ymin,ymax)*1.1
  }
  
  g <- ggplot(out)+
    geom_step(aes(time/365.241, est), size=1.001)
  
  if(conf.int){
    g <- g+
      geom_step(aes(time/365.241, lower))+
      geom_step(aes(time/365.241, upper))
  }

  g <- g+
    xlab(xlab)+
    ylab(ylab)
  
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

  if(!missing(ybreak)){
    g <- g +
      scale_y_continuous(expand = c(0, 0), limits = ylimits, breaks = ybreak)    
  } else{
    g <- g +
      scale_y_continuous(expand = c(0, 0), limits = ylimits)
  }
  if(ymirror){
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
