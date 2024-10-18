#### Inference for a competing risk model using RSS #### 
rm(list=ls())
library(nleqslv)

## parameter initialization 
n <- 40; p1 <- 0.10; 
a <- 0.01; b <- 1.3
alp <- 2.5; bet1 <- 0.8; bet2 <- 1.1; 
simul <- 11; 

## Hyper-parameter selection function 
hyper <- function(bt1, bt2, allp){ 
	b0 <- 1.4; c2 <- 1.8; b1 <- 1.2 
	a0 <- (bt1 + bt2)*b0; 
	c1 <- (bt1/bt2)*c2; 
	a1 <- allp*b1
	return(c(a0, b0, c1, c2, a1, b1))  
}

## Hyper-parameter selection function 
hyper_exp <- function(bt1, bt2, allp){
	b01 <- 1.4; c21 <- 1.8; b11 <- 1.2 
	a01 <- (bt1 + bt2)*b0; 
	c11 <- (bt1/bt2)*c2; 
	a11 <- allp*b1
	return(c(a01, b01, c11, c22, a11, b11))  
}
inf_prior_exp <- hyper(bet1, bet2, 1)
inf_prior_ray <- hyper(bet1, bet2, 2)
inf_prior_par <- hyper(bet1, bet2, 1)
inf_prior_bur <- hyper(bet1, bet2, 1)
inf_prior_wei <- hyper(bet1, bet2, alp)
non_prior_wei <- rep(0.0001, 6)

## Defining the form of g(x) for different distribution
gx_exp <- function(x) {x}
gx_ray <- function(x) {x}
gx_par <- function(x) {a * exp(x)}
gx_bur <- function(x) {(exp(x) - 1)^(1/b)}
gx_wei <- function(x) {x}

## Complete sample generation for GLD distribution using MinRSSU
sample_gen_MinRSSU <- function(n1, gx, bett, alph) {
	uu <- runif(n1)
	Y <- (((-1/alph) * log(1 - uu))^(1/bett))
	xs <- gx(Y)
	return(min(xs))
}

## MinRSS competing risk sample generation using MinRSSU with two causes
sample_MinRSSU_two_causes <- function(n1, gx, alp1, bett1, bett2) {
	bett12 <- bett1 + bett2
	xsamp <- sapply(1:n1, function(i) sample_gen_MinRSSU(i, gx,alp1, bett12))
	cause <- sample(1:2, size = n, replace = TRUE, prob = c(bett1/bett12, bett2/bett12))
	competing_data <- data.frame(failure_data = xsamp, failure_cause = cause)
	failure_unknown <- rbinom(n, 1, 1 - p1)
	competing_data$failure_cause[which(failure_unknown == 0)] <- 0

	delta_i <- ifelse(is.na(competing_data$failure_cause), 0, competing_data$failure_cause)
	delta_i[which(competing_data$censored == 0)] <- 0
	final_data <- data.frame(T_i = competing_data$failure_data, delta_i = delta_i)
	return(final_data)
}
final_exp_MinRSSU_two_causes <- sample_MinRSSU_two_causes(n, gx_exp, 1, bet1, bet2)
final_ray_MinRSSU_two_causes <- sample_MinRSSU_two_causes(n, gx_ray, 2, bet1, bet2)
final_par_MinRSSU_two_causes <- sample_MinRSSU_two_causes(n, gx_par, 1, bet1, bet2)
final_bur_MinRSSU_two_causes <- sample_MinRSSU_two_causes(n, gx_bur, 1, bet1, bet2)
final_wei_MinRSSU_two_causes <- sample_MinRSSU_two_causes(n, gx_wei,alp, bet1, bet2)

# final_exp_MinRSSU_two_causes
# final_ray_MinRSSU_two_causes
# final_par_MinRSSU_two_causes
# final_bur_MinRSSU_two_causes
# final_wei_MinRSSU_two_causes

# Program for MLE and Bayes estimation for Weibull distribution
estimation_wei <- function(xsrt, final, priors, q1, q2){
	x1 <- final_wei_MinRSSU_two_causes$T_i;                 # Total observation corresponding to time in Weibull distribution
	delta <- final_wei_MinRSSU_two_causes$delta_i;  
	n1 <- length(which(delta == 1)) 						# Number of observation due to casue1 in Weibull distribution
	n2 <- length(which(delta == 2)) 						# Number of observation due to cause 2 in Weibull distribution
	n0 <- length(which(delta == 0)) 						# Number of observation due to unknown cause in Weibull distribution
	
	# print(list(x1, n0, n1, n2))
	## Maximum Likelihood estimation 
	equations <- function(alpha) {
		psi_alpha <- sum(1:length(x1) * x1^alpha ) #psi _alpha
		psii_alpha <- sum(1:length(x1) * x1^alpha * log(x1)) #psi_das_alpha
		equ<- n/alpha + sum(log(x1)) - (n*psii_alpha)/psi_alpha
		return(equ)
	}
	solution <- nleqslv(xsrt, equations)
	alpha_hat <- solution$x
	psi_alpha_est <- sum(1:length(x1) * x1^alpha_hat)
	beta1_hat <- n1*n/((n1 + n2)*(psi_alpha_est)) 		# beta1 in Exponential distribution
    beta2_hat <- n2*n/((n1 + n2)*(psi_alpha_est)) 		# beta2 in Exponential distribution

	# Fisher Information matrix when alpha is unknown
	fisher_info_wei <- function(ml){
		alpp <- ml[1]; bett1 <- ml[2]; bett2 <- ml[3]; 
		psi_alpha <- sum(1:length(x1) * x1^alpp )             				# psi_alpha
		psii_alpha <- sum(1:length(x1) * x1^alpp * log(x1))  				# psi_alpha_das
		psiii_alpha <- sum(1:length(x1) * x1^alpp * (log(x1))^2) 			# psi_alpha_double_das
		f_matrix <- matrix(0,3,3);
		f_matrix[1,1] <- -n/alpp^2 - n*psiii_alpha/psi_alpha
		f_matrix[2,2] <- -n1/(bett1^2) - n0/((bett1 + bett2)^2); 
		f_matrix[3,3] <- -n2/(bett2^2) - n0/((bett1 + bett2)^2); 
		f_matrix[1,2] <- f_matrix[2,1] <- f_matrix[1,3] <- f_matrix[3,1] <- -psii_alpha ;  
		f_matrix[3,2] <- f_matrix[2,3] <- - n0/((bett1 + bett2)^2);
		return(f_matrix)
	}
	fisher_matrix <- fisher_info_wei(c(alpha_hat, beta1_hat, beta2_hat))
	var_matrix <- -solve(fisher_matrix)
	# if(var_matrix[1,1] < 0 || var_matrix[2,2] < 0 || var_matrix[3,3] < 0){
		# var_matrix[1,1] = abs(var_matrix[1,1]) & var_matrix[2,2] = abs(var_matrix[2,2]) & var_matrix[3,3] = abs(var_matrix[3,3])
	# }
	if(var_matrix[1,1] < 0){var_matrix[1,1] <- abs(var_matrix[1,1])}
	if(var_matrix[2,2] < 0){var_matrix[2,2] <- abs(var_matrix[2,2])}
	if(var_matrix[3,3] < 0){var_matrix[3,3] <- abs(var_matrix[3,3])}
	alp_lw  <- alpha_hat - 1.96*sqrt(var_matrix[1,1]); 
	alp_up  <- alpha_hat + 1.96*sqrt(var_matrix[1,1]); 
	bet1_lw <- beta1_hat - 1.96*sqrt(var_matrix[2,2]); 
	bet1_up <- beta1_hat + 1.96*sqrt(var_matrix[2,2]);
	bet2_lw <- beta2_hat - 1.96*sqrt(var_matrix[3,3]); 
	bet2_up <- beta2_hat + 1.96*sqrt(var_matrix[3,3]); 

	## Bayes estimation under without restriction 
	postSS <- 10000; los <- 0.05 
	a0 <- priors[1]; b0 <- priors[2]; c1 <- priors[3]; c2 <- priors[4]; a1 <- priors[5]; b1 <- priors[6];
	baybt1 <- baybt2 <- bayallp <- W_alp <- bt0 <- c(0); 
	bayallp[1] <- alpha_hat 
	pi_allp <- function(allp) {
		psi_alpha <- sum(1:length(x1) * x1^allp)  
		fun_val <- (((allp^(n + c1 - 1)) * (exp(-c2 * allp)) * (prod(x1^allp))) / ((b0 + psi_alpha)^(a0 + n))); 
		return(fun_val)
	}

	for(i1 in 1:postSS){
	temp <- rnorm(1,bayallp[i1], sqrt(var_matrix[1,1]))   
		ratio <- pi_allp(temp)/pi_allp(bayallp[i1])
		ratio[is.nan(ratio)] <- 0.5
		#print(ratio)
		rho <- min(1, ratio)
		u <- runif(1)
		if(u <= rho) {
			bayallp[i1+1] <- temp;
		} else {
			bayallp[i1+1] <- bayallp[i1];
		}
		bt0[i1] <- rgamma(1,a0 + n, b0 + sum(1:length(x1) * x1^bayallp[i1]))                #Generating thta0=(thta1 + thta2) from gamma distribution
		baybt0 <- rbeta(1,n1 + c1,n2 + c2)                                                  #Generate random thta
		baybt1[i1] <- bt0[i1]*baybt0; 														#Generated value of theta1
		baybt2[i1] <- bt0[i1] - baybt1[i1]													#Generated value of theta2
	}                                                         
	bay_bt1 <- mean(baybt1)																   #These are the bayes estimate
	bay_bt2 <- mean(baybt2)
	bay_alp <- mean(bayallp)
	# print(c(bay_allp, bay_bt1, bay_bt2))
	
	bay_bt1_LI1 <- (-1/q1)*log(mean(exp(-q1*baybt1))); 									   #These are the bayes estimate under LINEX loss function with positive parameter
	bay_bt2_LI1 <- (-1/q1)*log(mean(exp(-q1*baybt2)));
	bay_alp_LI1 <- (-1/q1)*log(mean(exp(-q1*bayallp))); 
	
	bay_bt1_LI2 <- (-1/q2)*log(mean(exp(-q2*baybt1))); 									   #These are the bayes estimate under LINEX loss function with negative parameter
	bay_bt2_LI2 <- (-1/q2)*log(mean(exp(-q2*baybt2)));
	bay_alp_LI2 <- (-1/q2)*log(mean(exp(-q2*bayallp))); 
	
	baybet1sort <- sort(baybt1); baybet2sort <- sort(baybt2); bayallpsort <- sort(bayallp); 
	bayes_bet1_low <- bayes_bet1_upp <- bayes_bet1_len <- c(0);
	bayes_bet2_low <- bayes_bet2_upp <- bayes_bet2_len <- c(0);	
	bayes_alpp_low <- bayes_alpp_upp <- bayes_alpp_len <- c(0);	
	
	for(k1 in 1:(postSS*los)){
		bayes_bet1_low[k1] <- baybet1sort[k1]
		bayes_bet1_upp[k1] <- baybet1sort[k1 + postSS*(1-los)]
		bayes_bet1_len[k1] <- bayes_bet1_upp[k1] - bayes_bet1_low[k1]   
		bayes_bet2_low[k1] <- baybet2sort[k1]
		bayes_bet2_upp[k1] <- baybet2sort[k1 + postSS*(1-los)]
		bayes_bet2_len[k1] <- bayes_bet2_upp[k1] - bayes_bet2_low[k1] 
		bayes_alpp_low[k1] <- bayallpsort[k1]
		bayes_alpp_upp[k1] <- bayallpsort[k1 + postSS*(1-los)]
		bayes_alpp_len[k1] <- bayes_alpp_upp[k1] - bayes_alpp_low[k1]
	}

	min_diff_bet1 <- which(bayes_bet1_len == min(bayes_bet1_len))[1]  
	min_diff_bet2 <- which(bayes_bet2_len == min(bayes_bet2_len))[1]
	min_diff_alpp <- which(bayes_alpp_len == min(bayes_alpp_len))[1]
	
	hbet1_lw <- bayes_bet1_low[min_diff_bet1]                                     			##These are the HPD confidence interval
	hbet1_up <- bayes_bet1_upp[min_diff_bet1]
	hbet2_lw <- bayes_bet2_low[min_diff_bet2]
	hbet2_up <- bayes_bet2_upp[min_diff_bet2]  
	halpp_lw <- bayes_alpp_low[min_diff_alpp]
	halpp_up <- bayes_alpp_upp[min_diff_alpp]  
	
	## Parameter estimation under restriction case 
	alpha_hat_WR <- alpha_hat; 
	if(n1 < n2){
		beta1_hat_WR <- beta1_hat; 
		beta2_hat_WR <- beta2_hat; 
	} else {
		psi_alpha_WR <- sum(1:length(x1) * x1^alpha_hat_WR); #psi _alpha
		beta1_hat_WR <- beta2_hat_WR <- n/(2*psi_alpha_WR); 
	}
	# print(c(n0, n1, n2, alpha_hat_WR, beta1_hat_WR, beta2_hat_WR))
	fisher_matrix_WR <- fisher_info_wei(c(alpha_hat_WR, beta1_hat_WR, beta2_hat_WR))
	var_matrix_WR <- -solve(fisher_matrix_WR)
	# print(var_matrix_WR)
	# if(var_matrix_WR[1,1] < 0 || var_matrix_WR[2,2] < 0 || var_matrix_WR[3,3] < 0){
		# var_matrix_WR[1,1] = abs(var_matrix_WR[1,1]) && var_matrix_WR[2,2] = abs(var_matrix_WR[2,2]) && var_matrix_WR[3,3] = abs(var_matrix_WR[3,3])
	# }
	if(var_matrix_WR[1,1] < 0){var_matrix_WR[1,1] <- 0.5}
	if(var_matrix_WR[2,2] < 0){var_matrix_WR[2,2] <- 0.5}
	if(var_matrix_WR[3,3] < 0){var_matrix_WR[3,3] <- 0.5}
	# print(var_matrix_WR)
	alp_lw_WR  <- alpha_hat_WR - 1.96*sqrt(var_matrix_WR[1,1]); 
	alp_up_WR  <- alpha_hat_WR + 1.96*sqrt(var_matrix_WR[1,1]); 
	bet1_lw_WR <- beta1_hat_WR - 1.96*sqrt(var_matrix_WR[2,2]); 
	bet1_up_WR <- beta1_hat_WR + 1.96*sqrt(var_matrix_WR[2,2]);
	bet2_lw_WR <- beta2_hat_WR - 1.96*sqrt(var_matrix_WR[3,3]); 
	bet2_up_WR <- beta2_hat_WR + 1.96*sqrt(var_matrix_WR[3,3]); 
	
	baybt1_WR <- baybt2_WR <- bayallp_WR <- W_alp_WR <- bt0_WR <- hh_WR <- c(0); 
	bayallp_WR[1] <- alpha_hat_WR 
	pi_allp_WR <- function(allp) {
		psi_alpha <- sum(1:length(x1) * x1^allp)  
		fun_val <- (((allp^(n + c1 - 1)) * (exp(-c2 * allp)) * (prod(x1^allp))) / ((b0 + psi_alpha)^(a0 + n)))
		return(fun_val)
	}

	for(i1 in 1:postSS){
	temp <- rnorm(1,bayallp_WR[i1], sqrt(var_matrix_WR[1,1]))   
		ratio <- pi_allp_WR(temp)/pi_allp_WR(bayallp_WR[i1])
		ratio[is.nan(ratio)] <- 0.5
		#print(ratio)
		rho <- min(1, ratio)
		u <- runif(1)
		if(u <= rho) {
			bayallp_WR[i1+1] <- temp;
		} else {
			bayallp_WR[i1+1] <- bayallp_WR[i1];
		}
		bt0_WR[i1] <- rgamma(1,a0 + n, b0 + sum(1:length(x1) * x1^bayallp_WR[i1]))                		#Generating thta0=(thta1 + thta2) from gamma distribution
		baybt0_WR <- rbeta(1,n1 + c1,n2 + c2)                                                   		#Generate random thta
		baybt1_WR[i1] <- bt0_WR[i1]*baybt0_WR; 															#Generated value of theta1
		baybt2_WR[i1] <- bt0_WR[i1] - baybt1_WR[i1]													  	#Generated value of theta2
		baybt1_WR[i1] <- min(baybt1_WR[i1], baybt2_WR[i1])
		baybt2_WR[i1] <- max(baybt1_WR[i1], baybt2_WR[i1])
		hh_WR[i1] <- (((baybt1_WR[i1] + baybt2_WR[i1])^(n1 + n2))/((baybt1_WR[i1]^n2)*(baybt2_WR[i1]^n1)))
	}                                                         
	bay_bt1_WR <- sum(hh_WR*baybt1_WR)/sum(hh_WR);														#These are the bayes estimate
	bay_bt2_WR <- sum(hh_WR*baybt2_WR)/sum(hh_WR);
	bay_alp_WR <- mean(bayallp_WR);
	# print(baybt1_WR)
	
	bay_bt1_LI1_WR <- (-1/q1)*log(mean(exp(-q1*baybt1_WR))); 									   		#These are the bayes estimate under LINEX loss function with positive parameter
	bay_bt2_LI1_WR <- (-1/q1)*log(mean(exp(-q1*baybt2_WR)));
	bay_alp_LI1_WR <- (-1/q1)*log(mean(exp(-q1*bayallp_WR))); 
	
	bay_bt1_LI2_WR <- (-1/q2)*log(mean(exp(-q2*baybt1_WR))); 											#These are the bayes estimate under LINEX loss function with negative parameter
	bay_bt2_LI2_WR <- (-1/q2)*log(mean(exp(-q2*baybt2_WR)));
	bay_alp_LI2_WR <- (-1/q2)*log(mean(exp(-q2*bayallp_WR))); 
	
	baybet1sort_WR <- sort(baybt1_WR); baybet2sort_WR <- sort(baybt2_WR); bayallpsort_WR <- sort(bayallp_WR); 
	bayes_bet1_low_WR <- bayes_bet1_upp_WR <- bayes_bet1_len_WR <- c(0);
	bayes_bet2_low_WR <- bayes_bet2_upp_WR <- bayes_bet2_len_WR <- c(0);	
	bayes_alpp_low_WR <- bayes_alpp_upp_WR <- bayes_alpp_len_WR <- c(0);	
	
	for(k1 in 1:(postSS*los)){
		bayes_bet1_low_WR[k1] <- baybet1sort_WR[k1]
		bayes_bet1_upp_WR[k1] <- baybet1sort_WR[k1 + postSS*(1-los)]
		bayes_bet1_len_WR[k1] <- bayes_bet1_upp_WR[k1] - bayes_bet1_low_WR[k1]      
		bayes_bet2_low_WR[k1] <- baybet2sort_WR[k1]
		bayes_bet2_upp_WR[k1] <- baybet2sort_WR[k1 + postSS*(1-los)]
		bayes_bet2_len_WR[k1] <- bayes_bet2_upp_WR[k1] - bayes_bet2_low_WR[k1] 
		bayes_alpp_low_WR[k1] <- bayallpsort_WR[k1]
		bayes_alpp_upp_WR[k1] <- bayallpsort_WR[k1 + postSS*(1-los)]
		bayes_alpp_len_WR[k1] <- bayes_alpp_upp_WR[k1] - bayes_alpp_low_WR[k1]
	}

	min_diff_bet1_WR <- which(bayes_bet1_len_WR == min(bayes_bet1_len_WR))[1]  
	min_diff_bet2_WR <- which(bayes_bet2_len_WR == min(bayes_bet2_len_WR))[1]
	min_diff_alpp_WR <- which(bayes_alpp_len_WR == min(bayes_alpp_len_WR))[1]
	
	hbet1_lw_WR <- bayes_bet1_low_WR[min_diff_bet1_WR]                                     			##These are the HPD confidence interval
	hbet1_up_WR <- bayes_bet1_upp_WR[min_diff_bet1_WR]
	hbet2_lw_WR <- bayes_bet2_low_WR[min_diff_bet2_WR]
	hbet2_up_WR <- bayes_bet2_upp_WR[min_diff_bet2_WR]  
	halpp_lw_WR <- bayes_alpp_low_WR[min_diff_alpp_WR]
	halpp_up_WR <- bayes_alpp_upp_WR[min_diff_alpp_WR]  
	
	mle_WOR_wei <- c(alpha_hat, beta1_hat, beta2_hat, alp_lw, alp_up, bet1_lw, bet1_up, bet2_lw, bet2_up);
	bay_WOR_wei <- (c(bay_alp, bay_bt1, bay_bt2, bay_alp_LI1, bay_bt1_LI1, bay_bt2_LI1, bay_alp_LI2, bay_bt1_LI2, bay_bt2_LI2, 
				halpp_lw, halpp_up, hbet1_lw, hbet1_up, hbet2_lw, hbet2_up));
	mle_WR_wei  <- c(alpha_hat_WR, beta1_hat_WR, beta2_hat_WR, alp_lw_WR, alp_up_WR, bet1_lw_WR, bet1_up_WR, bet2_lw_WR, bet2_up_WR); 
	bay_WR_wei  <- (c(bay_alp_WR, bay_bt1_WR, bay_bt2_WR, bay_alp_LI1_WR, bay_bt1_LI1_WR, bay_bt2_LI1_WR, bay_alp_LI2_WR, bay_bt1_LI2_WR, bay_bt2_LI2_WR, 
				halpp_lw_WR, halpp_up_WR, hbet1_lw_WR, hbet1_up_WR, hbet2_lw_WR, hbet2_up_WR));
	return(list(mle_WOR_wei, bay_WOR_wei, mle_WR_wei, bay_WR_wei))
}
xstart <- c(alp - 0.1)
est_inf_result_wei <- estimation_wei(xstart, final_wei_MinRSSU_two_causes, inf_prior_wei, 0.5, -0.5)
est_non_result_wei <- estimation_wei(xstart, final_wei_MinRSSU_two_causes, non_prior_wei, 0.5, -0.5)
wei_mle_wor <- 	 est_inf_result_wei[[1]]; 
wei_bay_inf_wor <- est_inf_result_wei[[2]];
wei_mle_wr  <-     est_inf_result_wei[[3]];  
wei_bay_inf_wr  <- est_inf_result_wei[[4]]; 
wei_bay_non_wor <- est_non_result_wei[[2]];
wei_bay_non_wr  <- est_non_result_wei[[4]]; 
wei_mle_wor; wei_mle_wr; wei_bay_inf_wor; wei_bay_inf_wr; wei_bay_non_wor; wei_bay_non_wr; 


## Apply simulation for 10000 iteration
wei_bett1_mle_est_wor <- wei_bett1_mle_bais_wor <- wei_bett1_mle_mse_wor <-  c(0); 
wei_bett2_mle_est_wor <- wei_bett2_mle_bais_wor <- wei_bett2_mle_mse_wor <-  c(0); 
wei_alppp_mle_est_wor <- wei_alppp_mle_bais_wor <- wei_alppp_mle_mse_wor <-  c(0); 
wei_bett1_aci_lw_wor <- wei_bett1_aci_up_wor <- wei_bett1_aci_len_wor <-  c(0); count_wei_bett1_aci_wor <- 0; 
wei_bett2_aci_lw_wor <- wei_bett2_aci_up_wor <- wei_bett2_aci_len_wor <-  c(0); count_wei_bett2_aci_wor <- 0; 
wei_alppp_aci_lw_wor <- wei_alppp_aci_up_wor <- wei_alppp_aci_len_wor <-  c(0); count_wei_alppp_aci_wor <- 0; 

wei_bett1_mle_est_wr <- wei_bett1_mle_bais_wr <- wei_bett1_mle_mse_wr <-  c(0); 
wei_bett2_mle_est_wr <- wei_bett2_mle_bais_wr <- wei_bett2_mle_mse_wr <-  c(0); 
wei_alppp_mle_est_wr <- wei_alppp_mle_bais_wr <- wei_alppp_mle_mse_wr <-  c(0); 
wei_bett1_aci_lw_wr <- wei_bett1_aci_up_wr <- wei_bett1_aci_len_wr <-  c(0); count_wei_bett1_aci_wr <- 0; 
wei_bett2_aci_lw_wr <- wei_bett2_aci_up_wr <- wei_bett2_aci_len_wr <-  c(0); count_wei_bett2_aci_wr <- 0; 
wei_alppp_aci_lw_wr <- wei_alppp_aci_up_wr <- wei_alppp_aci_len_wr <-  c(0); count_wei_alppp_aci_wr <- 0; 

wei_bett1_bay_inf_SE_est_wor <- wei_bett1_bay_inf_SE_bais_wor <- wei_bett1_bay_inf_SE_mse_wor <-  c(0); 
wei_bett2_bay_inf_SE_est_wor <- wei_bett2_bay_inf_SE_bais_wor <- wei_bett2_bay_inf_SE_mse_wor <-  c(0); 
wei_alppp_bay_inf_SE_est_wor <- wei_alppp_bay_inf_SE_bais_wor <- wei_alppp_bay_inf_SE_mse_wor <-  c(0); 
wei_bett1_bay_inf_LI1_est_wor <- wei_bett1_bay_inf_LI1_bais_wor <- wei_bett1_bay_inf_LI1_mse_wor <-  c(0); 
wei_bett2_bay_inf_LI1_est_wor <- wei_bett2_bay_inf_LI1_bais_wor <- wei_bett2_bay_inf_LI1_mse_wor <-  c(0); 
wei_alppp_bay_inf_LI1_est_wor <- wei_alppp_bay_inf_LI1_bais_wor <- wei_alppp_bay_inf_LI1_mse_wor <-  c(0); 
wei_bett1_bay_inf_LI2_est_wor <- wei_bett1_bay_inf_LI2_bais_wor <- wei_bett1_bay_inf_LI2_mse_wor <-  c(0); 
wei_bett2_bay_inf_LI2_est_wor <- wei_bett2_bay_inf_LI2_bais_wor <- wei_bett2_bay_inf_LI2_mse_wor <-  c(0); 
wei_alppp_bay_inf_LI2_est_wor <- wei_alppp_bay_inf_LI2_bais_wor <- wei_alppp_bay_inf_LI2_mse_wor <-  c(0); 
wei_bett1_hpd_inf_lw_wor <- wei_bett1_hpd_inf_up_wor <- wei_bett1_hpd_inf_len_wor <-  c(0); count_wei_bett1_hpd_inf_wor <- 0; 
wei_bett2_hpd_inf_lw_wor <- wei_bett2_hpd_inf_up_wor <- wei_bett2_hpd_inf_len_wor <-  c(0); count_wei_bett2_hpd_inf_wor <- 0; 
wei_alppp_hpd_inf_lw_wor <- wei_alppp_hpd_inf_up_wor <- wei_alppp_hpd_inf_len_wor <-  c(0); count_wei_alppp_hpd_inf_wor <- 0; 

wei_bett1_bay_inf_SE_est_wr <- wei_bett1_bay_inf_SE_bais_wr <- wei_bett1_bay_inf_SE_mse_wr <-  c(0); 
wei_bett2_bay_inf_SE_est_wr <- wei_bett2_bay_inf_SE_bais_wr <- wei_bett2_bay_inf_SE_mse_wr <-  c(0); 
wei_alppp_bay_inf_SE_est_wr <- wei_alppp_bay_inf_SE_bais_wr <- wei_alppp_bay_inf_SE_mse_wr <-  c(0); 
wei_bett1_bay_inf_LI1_est_wr <- wei_bett1_bay_inf_LI1_bais_wr <- wei_bett1_bay_inf_LI1_mse_wr <-  c(0); 
wei_bett2_bay_inf_LI1_est_wr <- wei_bett2_bay_inf_LI1_bais_wr <- wei_bett2_bay_inf_LI1_mse_wr <-  c(0); 
wei_alppp_bay_inf_LI1_est_wr <- wei_alppp_bay_inf_LI1_bais_wr <- wei_alppp_bay_inf_LI1_mse_wr <-  c(0); 
wei_bett1_bay_inf_LI2_est_wr <- wei_bett1_bay_inf_LI2_bais_wr <- wei_bett1_bay_inf_LI2_mse_wr <-  c(0); 
wei_bett2_bay_inf_LI2_est_wr <- wei_bett2_bay_inf_LI2_bais_wr <- wei_bett2_bay_inf_LI2_mse_wr <-  c(0); 
wei_alppp_bay_inf_LI2_est_wr <- wei_alppp_bay_inf_LI2_bais_wr <- wei_alppp_bay_inf_LI2_mse_wr <-  c(0); 
wei_bett1_hpd_inf_lw_wr <- wei_bett1_hpd_inf_up_wr <- wei_bett1_hpd_inf_len_wr <-  c(0); count_wei_bett1_hpd_inf_wr <- 0; 
wei_bett2_hpd_inf_lw_wr <- wei_bett2_hpd_inf_up_wr <- wei_bett2_hpd_inf_len_wr <-  c(0); count_wei_bett2_hpd_inf_wr <- 0; 
wei_alppp_hpd_inf_lw_wr <- wei_alppp_hpd_inf_up_wr <- wei_alppp_hpd_inf_len_wr <-  c(0); count_wei_alppp_hpd_inf_wr <- 0; 

wei_bett1_bay_non_SE_est_wor <- wei_bett1_bay_non_SE_bais_wor <- wei_bett1_bay_non_SE_mse_wor <-  c(0); 
wei_bett2_bay_non_SE_est_wor <- wei_bett2_bay_non_SE_bais_wor <- wei_bett2_bay_non_SE_mse_wor <-  c(0); 
wei_alppp_bay_non_SE_est_wor <- wei_alppp_bay_non_SE_bais_wor <- wei_alppp_bay_non_SE_mse_wor <-  c(0); 
wei_bett1_bay_non_LI1_est_wor <- wei_bett1_bay_non_LI1_bais_wor <- wei_bett1_bay_non_LI1_mse_wor <-  c(0); 
wei_bett2_bay_non_LI1_est_wor <- wei_bett2_bay_non_LI1_bais_wor <- wei_bett2_bay_non_LI1_mse_wor <-  c(0); 
wei_alppp_bay_non_LI1_est_wor <- wei_alppp_bay_non_LI1_bais_wor <- wei_alppp_bay_non_LI1_mse_wor <-  c(0); 
wei_bett1_bay_non_LI2_est_wor <- wei_bett1_bay_non_LI2_bais_wor <- wei_bett1_bay_non_LI2_mse_wor <-  c(0); 
wei_bett2_bay_non_LI2_est_wor <- wei_bett2_bay_non_LI2_bais_wor <- wei_bett2_bay_non_LI2_mse_wor <-  c(0); 
wei_alppp_bay_non_LI2_est_wor <- wei_alppp_bay_non_LI2_bais_wor <- wei_alppp_bay_non_LI2_mse_wor <-  c(0); 
wei_bett1_hpd_non_lw_wor <- wei_bett1_hpd_non_up_wor <- wei_bett1_hpd_non_len_wor <-  c(0); count_wei_bett1_hpd_non_wor <- 0; 
wei_bett2_hpd_non_lw_wor <- wei_bett2_hpd_non_up_wor <- wei_bett2_hpd_non_len_wor <-  c(0); count_wei_bett2_hpd_non_wor <- 0; 
wei_alppp_hpd_non_lw_wor <- wei_alppp_hpd_non_up_wor <- wei_alppp_hpd_non_len_wor <-  c(0); count_wei_alppp_hpd_non_wor <- 0; 

wei_bett1_bay_non_SE_est_wr <- wei_bett1_bay_non_SE_bais_wr <- wei_bett1_bay_non_SE_mse_wr <-  c(0); 
wei_bett2_bay_non_SE_est_wr <- wei_bett2_bay_non_SE_bais_wr <- wei_bett2_bay_non_SE_mse_wr <-  c(0); 
wei_alppp_bay_non_SE_est_wr <- wei_alppp_bay_non_SE_bais_wr <- wei_alppp_bay_non_SE_mse_wr <-  c(0); 
wei_bett1_bay_non_LI1_est_wr <- wei_bett1_bay_non_LI1_bais_wr <- wei_bett1_bay_non_LI1_mse_wr <-  c(0); 
wei_bett2_bay_non_LI1_est_wr <- wei_bett2_bay_non_LI1_bais_wr <- wei_bett2_bay_non_LI1_mse_wr <-  c(0); 
wei_alppp_bay_non_LI1_est_wr <- wei_alppp_bay_non_LI1_bais_wr <- wei_alppp_bay_non_LI1_mse_wr <-  c(0); 
wei_bett1_bay_non_LI2_est_wr <- wei_bett1_bay_non_LI2_bais_wr <- wei_bett1_bay_non_LI2_mse_wr <-  c(0); 
wei_bett2_bay_non_LI2_est_wr <- wei_bett2_bay_non_LI2_bais_wr <- wei_bett2_bay_non_LI2_mse_wr <-  c(0); 
wei_alppp_bay_non_LI2_est_wr <- wei_alppp_bay_non_LI2_bais_wr <- wei_alppp_bay_non_LI2_mse_wr <-  c(0); 
wei_bett1_hpd_non_lw_wr <- wei_bett1_hpd_non_up_wr <- wei_bett1_hpd_non_len_wr <-  c(0); count_wei_bett1_hpd_non_wr <- 0; 
wei_bett2_hpd_non_lw_wr <- wei_bett2_hpd_non_up_wr <- wei_bett2_hpd_non_len_wr <-  c(0); count_wei_bett2_hpd_non_wr <- 0; 
wei_alppp_hpd_non_lw_wr <- wei_alppp_hpd_non_up_wr <- wei_alppp_hpd_non_len_wr <-  c(0); count_wei_alppp_hpd_non_wr <- 0; 


for(l1 in 1:simul){
	final_wei_MinRSSU_two_causes <- sample_MinRSSU_two_causes(n, gx_wei,alp, bet1, bet2)
	est_inf_wei <- estimation_wei(xstart, final_wei_MinRSSU_two_causes, inf_prior_wei, 0.5, -0.5);
	est_non_wei <- estimation_wei(xstart, final_wei_MinRSSU_two_causes, non_prior_wei, 0.5, -0.5);
	wei_mle_est_wor 		<- est_inf_wei[[1]]; 
	wei_bay_inf_est_wor     <- est_inf_wei[[2]]; 
	wei_mle_est_wr 			<- est_inf_wei[[3]]; 
	wei_bay_inf_est_wr 		<- est_inf_wei[[4]];
	wei_bay_non_est_wor 	<- est_non_wei[[2]];
	wei_bay_non_est_wr 		<- est_non_wei[[4]];
	
	wei_alppp_mle_est_wor[l1] <-  wei_mle_est_wor[1]; wei_alppp_mle_bais_wor[l1] <- wei_alppp_mle_est_wor[l1] - alp; wei_alppp_mle_mse_wor[l1] <- (wei_alppp_mle_est_wor[l1] - alp)^2;
	wei_bett1_mle_est_wor[l1] <-  wei_mle_est_wor[2]; wei_bett1_mle_bais_wor[l1] <- wei_bett1_mle_est_wor[l1] - bet1; wei_bett1_mle_mse_wor[l1] <- (wei_bett1_mle_est_wor[l1] - bet1)^2;
	wei_bett2_mle_est_wor[l1] <-  wei_mle_est_wor[3]; wei_bett2_mle_bais_wor[l1] <- wei_bett2_mle_est_wor[l1] - bet2; wei_bett2_mle_mse_wor[l1] <- (wei_bett2_mle_est_wor[l1] - bet2)^2;
	wei_alppp_aci_lw_wor[l1]  <-  wei_mle_est_wor[4]; wei_alppp_aci_up_wor[l1]  <-  wei_mle_est_wor[5];	wei_alppp_aci_len_wor[l1] <- wei_alppp_aci_up_wor[l1] - wei_alppp_aci_lw_wor[l1];
	wei_bett1_aci_lw_wor[l1]  <-  wei_mle_est_wor[6]; wei_bett1_aci_up_wor[l1]  <-  wei_mle_est_wor[7];	wei_bett1_aci_len_wor[l1] <- wei_bett1_aci_up_wor[l1] - wei_bett1_aci_lw_wor[l1]; 
	wei_bett2_aci_lw_wor[l1]  <-  wei_mle_est_wor[8]; wei_bett2_aci_up_wor[l1]  <-  wei_mle_est_wor[9];	wei_bett2_aci_len_wor[l1] <- wei_bett2_aci_up_wor[l1] - wei_bett2_aci_lw_wor[l1]; 
	if(wei_alppp_aci_lw_wor[l1] < alp && wei_alppp_aci_up_wor[l1] > alp){count_wei_alppp_aci_wor <- count_wei_alppp_aci_wor + 1};
	if(wei_bett1_aci_lw_wor[l1] < bet1 && wei_bett1_aci_up_wor[l1] > bet1){count_wei_bett1_aci_wor <- count_wei_bett1_aci_wor + 1};			
	if(wei_bett2_aci_lw_wor[l1] < bet2 && wei_bett2_aci_up_wor[l1] > bet2){count_wei_bett2_aci_wor <- count_wei_bett2_aci_wor + 1};
	
	wei_alppp_mle_est_wr[l1] <-  wei_mle_est_wr[1]; wei_alppp_mle_bais_wr[l1] <- wei_alppp_mle_est_wr[l1] - alp; wei_alppp_mle_mse_wr[l1] <- (wei_alppp_mle_est_wr[l1] - alp)^2;
	wei_bett1_mle_est_wr[l1] <-  wei_mle_est_wr[2]; wei_bett1_mle_bais_wr[l1] <- wei_bett1_mle_est_wr[l1] - bet1; wei_bett1_mle_mse_wr[l1] <- (wei_bett1_mle_est_wr[l1] - bet1)^2;
	wei_bett2_mle_est_wr[l1] <-  wei_mle_est_wr[3]; wei_bett2_mle_bais_wr[l1] <- wei_bett2_mle_est_wr[l1] - bet2; wei_bett2_mle_mse_wr[l1] <- (wei_bett2_mle_est_wr[l1] - bet2)^2;
	wei_alppp_aci_lw_wr[l1]  <-  wei_mle_est_wr[4]; wei_alppp_aci_up_wr[l1]  <-  wei_mle_est_wr[5];	wei_alppp_aci_len_wr[l1] <- wei_alppp_aci_up_wr[l1] - wei_alppp_aci_lw_wr[l1];
	wei_bett1_aci_lw_wr[l1]  <-  wei_mle_est_wr[6]; wei_bett1_aci_up_wr[l1]  <-  wei_mle_est_wr[7];	wei_bett1_aci_len_wr[l1] <- wei_bett1_aci_up_wr[l1] - wei_bett1_aci_lw_wr[l1]; 
	wei_bett2_aci_lw_wr[l1]  <-  wei_mle_est_wr[8]; wei_bett2_aci_up_wr[l1]  <-  wei_mle_est_wr[9];	wei_bett2_aci_len_wr[l1] <- wei_bett2_aci_up_wr[l1] - wei_bett2_aci_lw_wr[l1]; 		
	# print(c(wei_alppp_aci_lw_wr[l1], wei_alppp_aci_up_wr[l1]))
	if(wei_alppp_aci_lw_wr[l1] < alp && wei_alppp_aci_up_wr[l1] > alp){count_wei_alppp_aci_wr <- count_wei_alppp_aci_wr + 1};   
	if(wei_bett1_aci_lw_wr[l1] < bet1 && wei_bett1_aci_up_wr[l1] > bet1){count_wei_bett1_aci_wr <- count_wei_bett1_aci_wr + 1};			
	if(wei_bett2_aci_lw_wr[l1] < bet2 && wei_bett2_aci_up_wr[l1] > bet2){count_wei_bett2_aci_wr <- count_wei_bett2_aci_wr + 1};
	
	wei_alppp_bay_inf_SE_est_wor[l1] <-  wei_bay_inf_est_wor[1]; wei_alppp_bay_inf_SE_bais_wor[l1] <- wei_alppp_bay_inf_SE_est_wor[l1] - alp;  wei_alppp_bay_inf_SE_mse_wor[l1] <- (wei_alppp_bay_inf_SE_est_wor[l1] - alp)^2;
	wei_bett1_bay_inf_SE_est_wor[l1] <-  wei_bay_inf_est_wor[2]; wei_bett1_bay_inf_SE_bais_wor[l1] <- wei_bett1_bay_inf_SE_est_wor[l1] - bet1; wei_bett1_bay_inf_SE_mse_wor[l1] <- (wei_bett1_bay_inf_SE_est_wor[l1] - bet1)^2;
	wei_bett2_bay_inf_SE_est_wor[l1] <-  wei_bay_inf_est_wor[3]; wei_bett2_bay_inf_SE_bais_wor[l1] <- wei_bett2_bay_inf_SE_est_wor[l1] - bet2; wei_bett2_bay_inf_SE_mse_wor[l1] <- (wei_bett2_bay_inf_SE_est_wor[l1] - bet2)^2;
	wei_alppp_bay_inf_LI1_est_wor[l1] <-  wei_bay_inf_est_wor[4]; wei_alppp_bay_inf_LI1_bais_wor[l1] <- wei_alppp_bay_inf_LI1_est_wor[l1] - alp; wei_alppp_bay_inf_LI1_mse_wor[l1] <- (wei_alppp_bay_inf_LI1_est_wor[l1] - alp)^2;
	wei_bett1_bay_inf_LI1_est_wor[l1] <-  wei_bay_inf_est_wor[5]; wei_bett1_bay_inf_LI1_bais_wor[l1] <- wei_bett1_bay_inf_LI1_est_wor[l1] - bet1; wei_bett1_bay_inf_LI1_mse_wor[l1] <- (wei_bett1_bay_inf_LI1_est_wor[l1] - bet1)^2;
	wei_bett2_bay_inf_LI1_est_wor[l1] <-  wei_bay_inf_est_wor[6]; wei_bett2_bay_inf_LI1_bais_wor[l1] <- wei_bett2_bay_inf_LI1_est_wor[l1] - bet2; wei_bett2_bay_inf_LI1_mse_wor[l1] <- (wei_bett2_bay_inf_LI1_est_wor[l1] - bet2)^2;
	wei_alppp_bay_inf_LI2_est_wor[l1] <-  wei_bay_inf_est_wor[7]; wei_alppp_bay_inf_LI2_bais_wor[l1] <- wei_alppp_bay_inf_LI2_est_wor[l1] - alp; wei_alppp_bay_inf_LI2_mse_wor[l1] <- (wei_alppp_bay_inf_LI2_est_wor[l1] - alp)^2;
	wei_bett1_bay_inf_LI2_est_wor[l1] <-  wei_bay_inf_est_wor[8]; wei_bett1_bay_inf_LI2_bais_wor[l1] <- wei_bett1_bay_inf_LI2_est_wor[l1] - bet1; wei_bett1_bay_inf_LI2_mse_wor[l1] <- (wei_bett1_bay_inf_LI2_est_wor[l1] - bet1)^2;
	wei_bett2_bay_inf_LI2_est_wor[l1] <-  wei_bay_inf_est_wor[9]; wei_bett2_bay_inf_LI2_bais_wor[l1] <- wei_bett2_bay_inf_LI2_est_wor[l1] - bet2; wei_bett2_bay_inf_LI2_mse_wor[l1] <- (wei_bett2_bay_inf_LI2_est_wor[l1] - bet2)^2;
	wei_alppp_hpd_inf_lw_wor[l1]  <-  wei_bay_inf_est_wor[10]; wei_alppp_hpd_inf_up_wor[l1]  <-  wei_bay_inf_est_wor[11];	wei_alppp_hpd_inf_len_wor[l1] <- wei_alppp_hpd_inf_up_wor[l1] - wei_alppp_hpd_inf_lw_wor[l1]; 
	wei_bett1_hpd_inf_lw_wor[l1]  <-  wei_bay_inf_est_wor[12]; wei_bett1_hpd_inf_up_wor[l1]  <-  wei_bay_inf_est_wor[13];	wei_bett1_hpd_inf_len_wor[l1] <- wei_bett1_hpd_inf_up_wor[l1] - wei_bett1_hpd_inf_lw_wor[l1]; 
	wei_bett2_hpd_inf_lw_wor[l1]  <-  wei_bay_inf_est_wor[14]; wei_bett2_hpd_inf_up_wor[l1]  <-  wei_bay_inf_est_wor[15];	wei_bett2_hpd_inf_len_wor[l1] <- wei_bett2_hpd_inf_up_wor[l1] - wei_bett2_hpd_inf_lw_wor[l1];
	if(wei_alppp_hpd_inf_lw_wor[l1] < alp && wei_alppp_hpd_inf_up_wor[l1] > alp){count_wei_alppp_hpd_inf_wor <- count_wei_alppp_hpd_inf_wor + 1}; 	
	if(wei_bett1_hpd_inf_lw_wor[l1] < bet1 && wei_bett1_hpd_inf_up_wor[l1] > bet1){count_wei_bett1_hpd_inf_wor <- count_wei_bett1_hpd_inf_wor + 1};
	if(wei_bett2_hpd_inf_lw_wor[l1] < bet2 && wei_bett2_hpd_inf_up_wor[l1] > bet2){count_wei_bett2_hpd_inf_wor <- count_wei_bett2_hpd_inf_wor + 1};
	
	wei_alppp_bay_inf_SE_est_wr[l1] <-  wei_bay_inf_est_wr[1]; wei_alppp_bay_inf_SE_bais_wr[l1] <- wei_alppp_bay_inf_SE_est_wr[l1] - alp;  wei_alppp_bay_inf_SE_mse_wr[l1] <- (wei_alppp_bay_inf_SE_est_wr[l1] - alp)^2;
	wei_bett1_bay_inf_SE_est_wr[l1] <-  wei_bay_inf_est_wr[2]; wei_bett1_bay_inf_SE_bais_wr[l1] <- wei_bett1_bay_inf_SE_est_wr[l1] - bet1; wei_bett1_bay_inf_SE_mse_wr[l1] <- (wei_bett1_bay_inf_SE_est_wr[l1] - bet1)^2;
	wei_bett2_bay_inf_SE_est_wr[l1] <-  wei_bay_inf_est_wr[3]; wei_bett2_bay_inf_SE_bais_wr[l1] <- wei_bett2_bay_inf_SE_est_wr[l1] - bet2; wei_bett2_bay_inf_SE_mse_wr[l1] <- (wei_bett2_bay_inf_SE_est_wr[l1] - bet2)^2;
	wei_alppp_bay_inf_LI1_est_wr[l1] <-  wei_bay_inf_est_wr[4]; wei_alppp_bay_inf_LI1_bais_wr[l1] <- wei_alppp_bay_inf_LI1_est_wr[l1] - alp; wei_alppp_bay_inf_LI1_mse_wr[l1] <- (wei_alppp_bay_inf_LI1_est_wr[l1] - alp)^2;
	wei_bett1_bay_inf_LI1_est_wr[l1] <-  wei_bay_inf_est_wr[5]; wei_bett1_bay_inf_LI1_bais_wr[l1] <- wei_bett1_bay_inf_LI1_est_wr[l1] - bet1; wei_bett1_bay_inf_LI1_mse_wr[l1] <- (wei_bett1_bay_inf_LI1_est_wr[l1] - bet1)^2;
	wei_bett2_bay_inf_LI1_est_wr[l1] <-  wei_bay_inf_est_wr[6]; wei_bett2_bay_inf_LI1_bais_wr[l1] <- wei_bett2_bay_inf_LI1_est_wr[l1] - bet2; wei_bett2_bay_inf_LI1_mse_wr[l1] <- (wei_bett2_bay_inf_LI1_est_wr[l1] - bet2)^2;
	wei_alppp_bay_inf_LI2_est_wr[l1] <-  wei_bay_inf_est_wr[7]; wei_alppp_bay_inf_LI2_bais_wr[l1] <- wei_alppp_bay_inf_LI2_est_wr[l1] - alp; wei_alppp_bay_inf_LI2_mse_wr[l1] <- (wei_alppp_bay_inf_LI2_est_wr[l1] - alp)^2;
	wei_bett1_bay_inf_LI2_est_wr[l1] <-  wei_bay_inf_est_wr[8]; wei_bett1_bay_inf_LI2_bais_wr[l1] <- wei_bett1_bay_inf_LI2_est_wr[l1] - bet1; wei_bett1_bay_inf_LI2_mse_wr[l1] <- (wei_bett1_bay_inf_LI2_est_wr[l1] - bet1)^2;
	wei_bett2_bay_inf_LI2_est_wr[l1] <-  wei_bay_inf_est_wr[9]; wei_bett2_bay_inf_LI2_bais_wr[l1] <- wei_bett2_bay_inf_LI2_est_wr[l1] - bet2; wei_bett2_bay_inf_LI2_mse_wr[l1] <- (wei_bett2_bay_inf_LI2_est_wr[l1] - bet2)^2;
	wei_alppp_hpd_inf_lw_wr[l1]  <-  wei_bay_inf_est_wr[10]; wei_alppp_hpd_inf_up_wr[l1]  <-  wei_bay_inf_est_wr[11];	wei_alppp_hpd_inf_len_wr[l1] <- wei_alppp_hpd_inf_up_wr[l1] - wei_alppp_hpd_inf_lw_wr[l1]; 
	wei_bett1_hpd_inf_lw_wr[l1]  <-  wei_bay_inf_est_wr[12]; wei_bett1_hpd_inf_up_wr[l1]  <-  wei_bay_inf_est_wr[13];	wei_bett1_hpd_inf_len_wr[l1] <- wei_bett1_hpd_inf_up_wr[l1] - wei_bett1_hpd_inf_lw_wr[l1]; 
	wei_bett2_hpd_inf_lw_wr[l1]  <-  wei_bay_inf_est_wr[14]; wei_bett2_hpd_inf_up_wr[l1]  <-  wei_bay_inf_est_wr[15];	wei_bett2_hpd_inf_len_wr[l1] <- wei_bett2_hpd_inf_up_wr[l1] - wei_bett2_hpd_inf_lw_wr[l1]; 
	if(wei_alppp_hpd_inf_lw_wr[l1] < alp && wei_alppp_hpd_inf_up_wr[l1] > alp){count_wei_alppp_hpd_inf_wr <- count_wei_alppp_hpd_inf_wr + 1};
	if(wei_bett1_hpd_inf_lw_wr[l1] < bet1 && wei_bett1_hpd_inf_up_wr[l1] > bet1){count_wei_bett1_hpd_inf_wr <- count_wei_bett1_hpd_inf_wr + 1};
	if(wei_bett2_hpd_inf_lw_wr[l1] < bet2 && wei_bett2_hpd_inf_up_wr[l1] > bet2){count_wei_bett2_hpd_inf_wr <- count_wei_bett2_hpd_inf_wr + 1};
	
	wei_alppp_bay_non_SE_est_wor[l1] <-  wei_bay_non_est_wor[1]; wei_alppp_bay_non_SE_bais_wor[l1] <- wei_alppp_bay_non_SE_est_wor[l1] - alp;  wei_alppp_bay_non_SE_mse_wor[l1] <- (wei_alppp_bay_non_SE_est_wor[l1] - alp)^2;
	wei_bett1_bay_non_SE_est_wor[l1] <-  wei_bay_non_est_wor[2]; wei_bett1_bay_non_SE_bais_wor[l1] <- wei_bett1_bay_non_SE_est_wor[l1] - bet1; wei_bett1_bay_non_SE_mse_wor[l1] <- (wei_bett1_bay_non_SE_est_wor[l1] - bet1)^2;
	wei_bett2_bay_non_SE_est_wor[l1] <-  wei_bay_non_est_wor[3]; wei_bett2_bay_non_SE_bais_wor[l1] <- wei_bett2_bay_non_SE_est_wor[l1] - bet2; wei_bett2_bay_non_SE_mse_wor[l1] <- (wei_bett2_bay_non_SE_est_wor[l1] - bet2)^2;
	wei_alppp_bay_non_LI1_est_wor[l1] <-  wei_bay_non_est_wor[4]; wei_alppp_bay_non_LI1_bais_wor[l1] <- wei_alppp_bay_non_LI1_est_wor[l1] - alp; wei_alppp_bay_non_LI1_mse_wor[l1] <- (wei_alppp_bay_non_LI1_est_wor[l1] - alp)^2;
	wei_bett1_bay_non_LI1_est_wor[l1] <-  wei_bay_non_est_wor[5]; wei_bett1_bay_non_LI1_bais_wor[l1] <- wei_bett1_bay_non_LI1_est_wor[l1] - bet1; wei_bett1_bay_non_LI1_mse_wor[l1] <- (wei_bett1_bay_non_LI1_est_wor[l1] - bet1)^2;
	wei_bett2_bay_non_LI1_est_wor[l1] <-  wei_bay_non_est_wor[6]; wei_bett2_bay_non_LI1_bais_wor[l1] <- wei_bett2_bay_non_LI1_est_wor[l1] - bet2; wei_bett2_bay_non_LI1_mse_wor[l1] <- (wei_bett2_bay_non_LI1_est_wor[l1] - bet2)^2;
	wei_alppp_bay_non_LI2_est_wor[l1] <-  wei_bay_non_est_wor[7]; wei_alppp_bay_non_LI2_bais_wor[l1] <- wei_alppp_bay_non_LI2_est_wor[l1] - alp; wei_alppp_bay_non_LI2_mse_wor[l1] <- (wei_alppp_bay_non_LI2_est_wor[l1] - alp)^2;
	wei_bett1_bay_non_LI2_est_wor[l1] <-  wei_bay_non_est_wor[8]; wei_bett1_bay_non_LI2_bais_wor[l1] <- wei_bett1_bay_non_LI2_est_wor[l1] - bet1; wei_bett1_bay_non_LI2_mse_wor[l1] <- (wei_bett1_bay_non_LI2_est_wor[l1] - bet1)^2;
	wei_bett2_bay_non_LI2_est_wor[l1] <-  wei_bay_non_est_wor[9]; wei_bett2_bay_non_LI2_bais_wor[l1] <- wei_bett2_bay_non_LI2_est_wor[l1] - bet2; wei_bett2_bay_non_LI2_mse_wor[l1] <- (wei_bett2_bay_non_LI2_est_wor[l1] - bet2)^2;
	wei_alppp_hpd_non_lw_wor[l1]  <-  wei_bay_non_est_wor[10]; wei_alppp_hpd_non_up_wor[l1]  <-  wei_bay_non_est_wor[11];	wei_alppp_hpd_non_len_wor[l1] <- wei_alppp_hpd_non_up_wor[l1] - wei_alppp_hpd_non_lw_wor[l1]; 
	wei_bett1_hpd_non_lw_wor[l1]  <-  wei_bay_non_est_wor[12]; wei_bett1_hpd_non_up_wor[l1]  <-  wei_bay_non_est_wor[13];	wei_bett1_hpd_non_len_wor[l1] <- wei_bett1_hpd_non_up_wor[l1] - wei_bett1_hpd_non_lw_wor[l1]; 
	wei_bett2_hpd_non_lw_wor[l1]  <-  wei_bay_non_est_wor[14]; wei_bett2_hpd_non_up_wor[l1]  <-  wei_bay_non_est_wor[15];	wei_bett2_hpd_non_len_wor[l1] <- wei_bett2_hpd_non_up_wor[l1] - wei_bett2_hpd_non_lw_wor[l1];
	if(wei_alppp_hpd_non_lw_wor[l1] < alp && wei_alppp_hpd_non_up_wor[l1] > alp){count_wei_alppp_hpd_non_wor <- count_wei_alppp_hpd_non_wor + 1}; 	
	if(wei_bett1_hpd_non_lw_wor[l1] < bet1 && wei_bett1_hpd_non_up_wor[l1] > bet1){count_wei_bett1_hpd_non_wor <- count_wei_bett1_hpd_non_wor + 1};
	if(wei_bett2_hpd_non_lw_wor[l1] < bet2 && wei_bett2_hpd_non_up_wor[l1] > bet2){count_wei_bett2_hpd_non_wor <- count_wei_bett2_hpd_non_wor + 1};
	
	wei_alppp_bay_non_SE_est_wr[l1] <-  wei_bay_non_est_wr[1]; wei_alppp_bay_non_SE_bais_wr[l1] <- wei_alppp_bay_non_SE_est_wr[l1] - alp;  wei_alppp_bay_non_SE_mse_wr[l1] <- (wei_alppp_bay_non_SE_est_wr[l1] - alp)^2;
	wei_bett1_bay_non_SE_est_wr[l1] <-  wei_bay_non_est_wr[2]; wei_bett1_bay_non_SE_bais_wr[l1] <- wei_bett1_bay_non_SE_est_wr[l1] - bet1; wei_bett1_bay_non_SE_mse_wr[l1] <- (wei_bett1_bay_non_SE_est_wr[l1] - bet1)^2;
	wei_bett2_bay_non_SE_est_wr[l1] <-  wei_bay_non_est_wr[3]; wei_bett2_bay_non_SE_bais_wr[l1] <- wei_bett2_bay_non_SE_est_wr[l1] - bet2; wei_bett2_bay_non_SE_mse_wr[l1] <- (wei_bett2_bay_non_SE_est_wr[l1] - bet2)^2;
	wei_alppp_bay_non_LI1_est_wr[l1] <-  wei_bay_non_est_wr[4]; wei_alppp_bay_non_LI1_bais_wr[l1] <- wei_alppp_bay_non_LI1_est_wr[l1] - alp; wei_alppp_bay_non_LI1_mse_wr[l1] <- (wei_alppp_bay_non_LI1_est_wr[l1] - alp)^2;
	wei_bett1_bay_non_LI1_est_wr[l1] <-  wei_bay_non_est_wr[5]; wei_bett1_bay_non_LI1_bais_wr[l1] <- wei_bett1_bay_non_LI1_est_wr[l1] - bet1; wei_bett1_bay_non_LI1_mse_wr[l1] <- (wei_bett1_bay_non_LI1_est_wr[l1] - bet1)^2;
	wei_bett2_bay_non_LI1_est_wr[l1] <-  wei_bay_non_est_wr[6]; wei_bett2_bay_non_LI1_bais_wr[l1] <- wei_bett2_bay_non_LI1_est_wr[l1] - bet2; wei_bett2_bay_non_LI1_mse_wr[l1] <- (wei_bett2_bay_non_LI1_est_wr[l1] - bet2)^2;
	wei_alppp_bay_non_LI2_est_wr[l1] <-  wei_bay_non_est_wr[7]; wei_alppp_bay_non_LI2_bais_wr[l1] <- wei_alppp_bay_non_LI2_est_wr[l1] - alp; wei_alppp_bay_non_LI2_mse_wr[l1] <- (wei_alppp_bay_non_LI2_est_wr[l1] - alp)^2;
	wei_bett1_bay_non_LI2_est_wr[l1] <-  wei_bay_non_est_wr[8]; wei_bett1_bay_non_LI2_bais_wr[l1] <- wei_bett1_bay_non_LI2_est_wr[l1] - bet1; wei_bett1_bay_non_LI2_mse_wr[l1] <- (wei_bett1_bay_non_LI2_est_wr[l1] - bet1)^2;
	wei_bett2_bay_non_LI2_est_wr[l1] <-  wei_bay_non_est_wr[9]; wei_bett2_bay_non_LI2_bais_wr[l1] <- wei_bett2_bay_non_LI2_est_wr[l1] - bet2; wei_bett2_bay_non_LI2_mse_wr[l1] <- (wei_bett2_bay_non_LI2_est_wr[l1] - bet2)^2;
	wei_alppp_hpd_non_lw_wr[l1]  <-  wei_bay_non_est_wr[10]; wei_alppp_hpd_non_up_wr[l1]  <-  wei_bay_non_est_wr[11];	wei_alppp_hpd_non_len_wr[l1] <- wei_alppp_hpd_non_up_wr[l1] - wei_alppp_hpd_non_lw_wr[l1]; 
	wei_bett1_hpd_non_lw_wr[l1]  <-  wei_bay_non_est_wr[12]; wei_bett1_hpd_non_up_wr[l1]  <-  wei_bay_non_est_wr[13];	wei_bett1_hpd_non_len_wr[l1] <- wei_bett1_hpd_non_up_wr[l1] - wei_bett1_hpd_non_lw_wr[l1]; 
	wei_bett2_hpd_non_lw_wr[l1]  <-  wei_bay_non_est_wr[14]; wei_bett2_hpd_non_up_wr[l1]  <-  wei_bay_non_est_wr[15];	wei_bett2_hpd_non_len_wr[l1] <- wei_bett2_hpd_non_up_wr[l1] - wei_bett2_hpd_non_lw_wr[l1]; 
	if(wei_alppp_hpd_non_lw_wr[l1] < alp && wei_alppp_hpd_non_up_wr[l1] > alp){count_wei_alppp_hpd_non_wr <- count_wei_alppp_hpd_non_wr + 1};
	if(wei_bett1_hpd_non_lw_wr[l1] < bet1 && wei_bett1_hpd_non_up_wr[l1] > bet1){count_wei_bett1_hpd_non_wr <- count_wei_bett1_hpd_non_wr + 1};
	if(wei_bett2_hpd_non_lw_wr[l1] < bet2 && wei_bett2_hpd_non_up_wr[l1] > bet2){count_wei_bett2_hpd_non_wr <- count_wei_bett2_hpd_non_wr + 1};
	
	cat("\n..... iteration is", l1)
}
wei_alppp_wor <- round(c(mean(wei_alppp_mle_est_wor), mean(wei_alppp_mle_mse_wor), mean(wei_alppp_aci_len_wor), count_wei_alppp_aci_wor/simul, 
				mean(wei_alppp_bay_inf_SE_est_wor), mean(wei_alppp_bay_inf_SE_mse_wor), mean(wei_alppp_bay_inf_LI1_est_wor), 
				mean(wei_alppp_bay_inf_LI1_mse_wor), mean(wei_alppp_bay_inf_LI2_est_wor), mean(wei_alppp_bay_inf_LI2_mse_wor), 
				mean(wei_alppp_hpd_inf_len_wor), count_wei_alppp_hpd_inf_wor/simul, mean(wei_alppp_bay_non_SE_est_wor), 
				mean(wei_alppp_bay_non_SE_mse_wor), mean(wei_alppp_bay_non_LI1_est_wor), mean(wei_alppp_bay_non_LI1_mse_wor), 
				mean(wei_alppp_bay_non_LI2_est_wor), mean(wei_alppp_bay_non_LI2_mse_wor), mean(wei_alppp_hpd_non_len_wor), 
				count_wei_alppp_hpd_non_wor/simul), 3)
wei_bett1_wor <- round(c(mean(wei_bett1_mle_est_wor), mean(wei_bett1_mle_mse_wor), mean(wei_bett1_aci_len_wor), count_wei_bett1_aci_wor/simul, 
				mean(wei_bett1_bay_inf_SE_est_wor), mean(wei_bett1_bay_inf_SE_mse_wor), mean(wei_bett1_bay_inf_LI1_est_wor), 
				mean(wei_bett1_bay_inf_LI1_mse_wor), mean(wei_bett1_bay_inf_LI2_est_wor), mean(wei_bett1_bay_inf_LI2_mse_wor), 
				mean(wei_bett1_hpd_inf_len_wor), count_wei_bett1_hpd_inf_wor/simul, mean(wei_bett1_bay_non_SE_est_wor), 
				mean(wei_bett1_bay_non_SE_mse_wor), mean(wei_bett1_bay_non_LI1_est_wor), mean(wei_bett1_bay_non_LI1_mse_wor), 
				mean(wei_bett1_bay_non_LI2_est_wor), mean(wei_bett1_bay_non_LI2_mse_wor), mean(wei_bett1_hpd_non_len_wor), 
				count_wei_bett1_hpd_non_wor/simul), 3)
wei_bett2_wor <- round(c(mean(wei_bett2_mle_est_wor), mean(wei_bett2_mle_mse_wor), mean(wei_bett2_aci_len_wor), count_wei_bett2_aci_wor/simul, 
				mean(wei_bett2_bay_inf_SE_est_wor), mean(wei_bett2_bay_inf_SE_mse_wor), mean(wei_bett2_bay_inf_LI1_est_wor), 
				mean(wei_bett2_bay_inf_LI1_mse_wor), mean(wei_bett2_bay_inf_LI2_est_wor), mean(wei_bett2_bay_inf_LI2_mse_wor), 
				mean(wei_bett2_hpd_inf_len_wor), count_wei_bett2_hpd_inf_wor/simul, mean(wei_bett2_bay_non_SE_est_wor), 
				mean(wei_bett2_bay_non_SE_mse_wor), mean(wei_bett2_bay_non_LI1_est_wor), mean(wei_bett2_bay_non_LI1_mse_wor), 
				mean(wei_bett2_bay_non_LI2_est_wor), mean(wei_bett2_bay_non_LI2_mse_wor), mean(wei_bett2_hpd_non_len_wor), 
				count_wei_bett2_hpd_non_wor/simul), 3)
wei_alppp_wr <- round(c(mean(wei_alppp_mle_est_wr), mean(wei_alppp_mle_mse_wr), mean(wei_alppp_aci_len_wr), count_wei_alppp_aci_wr/simul, 
				mean(wei_alppp_bay_inf_SE_est_wr), mean(wei_alppp_bay_inf_SE_mse_wr), mean(wei_alppp_bay_inf_LI1_est_wr), 
				mean(wei_alppp_bay_inf_LI1_mse_wr), mean(wei_alppp_bay_inf_LI2_est_wr), mean(wei_alppp_bay_inf_LI2_mse_wr), 
				mean(wei_alppp_hpd_inf_len_wr), count_wei_alppp_hpd_inf_wr/simul, mean(wei_alppp_bay_non_SE_est_wr), 
				mean(wei_alppp_bay_non_SE_mse_wr), mean(wei_alppp_bay_non_LI1_est_wr), mean(wei_alppp_bay_non_LI1_mse_wr), 
				mean(wei_alppp_bay_non_LI2_est_wr), mean(wei_alppp_bay_non_LI2_mse_wr), mean(wei_alppp_hpd_non_len_wr), 
				count_wei_alppp_hpd_non_wr/simul), 3)
wei_bett1_wr <- round(c(mean(wei_bett1_mle_est_wr), mean(wei_bett1_mle_mse_wr), mean(wei_bett1_aci_len_wr), count_wei_bett1_aci_wr/simul, 
				mean(wei_bett1_bay_inf_SE_est_wr), mean(wei_bett1_bay_inf_SE_mse_wr), mean(wei_bett1_bay_inf_LI1_est_wr), 
				mean(wei_bett1_bay_inf_LI1_mse_wr), mean(wei_bett1_bay_inf_LI2_est_wr), mean(wei_bett1_bay_inf_LI2_mse_wr), 
				mean(wei_bett1_hpd_inf_len_wr), count_wei_bett1_hpd_inf_wr/simul, mean(wei_bett1_bay_non_SE_est_wr), 
				mean(wei_bett1_bay_non_SE_mse_wr), mean(wei_bett1_bay_non_LI1_est_wr), mean(wei_bett1_bay_non_LI1_mse_wr), 
				mean(wei_bett1_bay_non_LI2_est_wr), mean(wei_bett1_bay_non_LI2_mse_wr), mean(wei_bett1_hpd_non_len_wr), 
				count_wei_bett1_hpd_non_wr/simul), 3)
wei_bett2_wr <- round(c(mean(wei_bett2_mle_est_wr), mean(wei_bett2_mle_mse_wr), mean(wei_bett2_aci_len_wr), count_wei_bett2_aci_wr/simul, 
				mean(wei_bett2_bay_inf_SE_est_wr), mean(wei_bett2_bay_inf_SE_mse_wr), mean(wei_bett2_bay_inf_LI1_est_wr), 
				mean(wei_bett2_bay_inf_LI1_mse_wr), mean(wei_bett2_bay_inf_LI2_est_wr), mean(wei_bett2_bay_inf_LI2_mse_wr), 
				mean(wei_bett2_hpd_inf_len_wr), count_wei_bett2_hpd_inf_wr/simul, mean(wei_bett2_bay_non_SE_est_wr), 
				mean(wei_bett2_bay_non_SE_mse_wr), mean(wei_bett2_bay_non_LI1_est_wr), mean(wei_bett2_bay_non_LI1_mse_wr), 
				mean(wei_bett2_bay_non_LI2_est_wr), mean(wei_bett2_bay_non_LI2_mse_wr), mean(wei_bett2_hpd_non_len_wr), 
				count_wei_bett2_hpd_non_wr/simul), 3)

wei_alppp_wor; wei_bett1_wor; wei_bett2_wor; wei_alppp_wr; wei_bett1_wr; wei_bett2_wr; 

noquote(paste0(wei_alppp_wor[1]," & ",wei_alppp_wor[2]," & ",wei_alppp_wor[5]," & ",wei_alppp_wor[6]," & ",wei_alppp_wor[7]," & ",wei_alppp_wor[8],
		" & ", wei_alppp_wor[9]," & ",wei_alppp_wor[10], " & ",wei_alppp_wor[13]," & ",wei_alppp_wor[14]," & ",wei_alppp_wor[15]," & ",
		wei_alppp_wor[16], " & ", wei_alppp_wor[17]," & ",wei_alppp_wor[18]))
noquote(paste0(wei_bett1_wor[1]," & ",wei_bett1_wor[2]," & ",wei_bett1_wor[5]," & ",wei_bett1_wor[6]," & ",wei_bett1_wor[7]," & ",wei_bett1_wor[8],
		" & ", wei_bett1_wor[9]," & ",wei_bett1_wor[10], " & ",wei_bett1_wor[13]," & ",wei_bett1_wor[14]," & ",wei_bett1_wor[15]," & ",
		wei_bett1_wor[16], " & ", wei_bett1_wor[17]," & ",wei_bett1_wor[18]))
noquote(paste0(wei_bett2_wor[1]," & ",wei_bett2_wor[2]," & ",wei_bett2_wor[5]," & ",wei_bett2_wor[6]," & ",wei_bett2_wor[7]," & ",wei_bett2_wor[8],
		" & ", wei_bett2_wor[9]," & ",wei_bett2_wor[10], " & ",wei_bett2_wor[13]," & ",wei_bett2_wor[14]," & ",wei_bett2_wor[15]," & ",
		wei_bett2_wor[16], " & ", wei_bett2_wor[17]," & ",wei_bett2_wor[18]))
noquote(paste0(wei_alppp_wr[1]," & ",wei_alppp_wr[2]," & ",wei_alppp_wr[5]," & ",wei_alppp_wr[6]," & ",wei_alppp_wr[7]," & ",wei_alppp_wr[8],
		" & ", wei_alppp_wr[9]," & ",wei_alppp_wr[10], " & ",wei_alppp_wr[13]," & ",wei_alppp_wr[14]," & ",wei_alppp_wr[15]," & ",
		wei_alppp_wr[16], " & ", wei_alppp_wr[17]," & ",wei_alppp_wr[18]))
noquote(paste0(wei_bett1_wr[1]," & ",wei_bett1_wr[2]," & ",wei_bett1_wr[5]," & ",wei_bett1_wr[6]," & ",wei_bett1_wr[7]," & ",wei_bett1_wr[8],
		" & ", wei_bett1_wr[9]," & ",wei_bett1_wr[10], " & ",wei_bett1_wr[13]," & ",wei_bett1_wr[14]," & ",wei_bett1_wr[15]," & ",
		wei_bett1_wr[16], " & ", wei_bett1_wr[17]," & ",wei_bett1_wr[18]))
noquote(paste0(wei_bett2_wr[1]," & ",wei_bett2_wr[2]," & ",wei_bett2_wr[5]," & ",wei_bett2_wr[6]," & ",wei_bett2_wr[7]," & ",wei_bett2_wr[8],
		" & ", wei_bett2_wr[9]," & ",wei_bett2_wr[10], " & ",wei_bett2_wr[13]," & ",wei_bett2_wr[14]," & ",wei_bett2_wr[15]," & ",
		wei_bett2_wr[16], " & ", wei_bett2_wr[17]," & ",wei_bett2_wr[18]))

noquote(paste0(wei_alppp_wor[3]," & ",wei_alppp_wor[4]," & ",wei_alppp_wor[11]," & ",wei_alppp_wor[12], " & ",wei_alppp_wor[19]," & ",wei_alppp_wor[20]))
noquote(paste0(wei_bett1_wor[3]," & ",wei_bett1_wor[4]," & ",wei_bett1_wor[11]," & ",wei_bett1_wor[12], " & ",wei_bett1_wor[19]," & ",wei_bett1_wor[20]))
noquote(paste0(wei_bett2_wor[3]," & ",wei_bett2_wor[4]," & ",wei_bett2_wor[11]," & ",wei_bett2_wor[12], " & ",wei_bett2_wor[19]," & ",wei_bett2_wor[20]))
noquote(paste0(wei_alppp_wr[3]," & ",wei_alppp_wr[4]," & ",wei_alppp_wr[11]," & ",wei_alppp_wr[12], " & ",wei_alppp_wr[19]," & ",wei_alppp_wr[20]))
noquote(paste0(wei_bett1_wr[3]," & ",wei_bett1_wr[4]," & ",wei_bett1_wr[11]," & ",wei_bett1_wr[12], " & ",wei_bett1_wr[19]," & ",wei_bett1_wr[20]))
noquote(paste0(wei_bett2_wr[3]," & ",wei_bett2_wr[4]," & ",wei_bett2_wr[11]," & ",wei_bett2_wr[12], " & ",wei_bett2_wr[19]," & ",wei_bett2_wr[20]))


