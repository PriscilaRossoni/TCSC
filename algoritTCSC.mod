
#
# A Mathematical Programming Approach for Allocation and Analysis of TCSC in Power Transmission Systems
# IEEE Latin America Transactions 2022 
# J. S. Pereira, E. A. Belati, C. F. Nascimento, P. F. Silva and P. Rossoni
#
# J. S. Pereira, Federal University of ABC, was with Federal University of ABC, Santo André, Brasil, (e-mail: j.pereira@ufabc.edu.br).
# E. A. Belati, Author is with Center for Engineering, Modeling and Applied Sciences (CECS), Federal University of ABC, Santo André, Brasil, (e-mail: edmarcio.belati@ufabc.edu.br).
# C. F. Nascimento, Author is with Center for Exact Sciences and Technology (CCET), Universidade Federal de São Carlos, Brasil, (e-mail: claudionor@ufscar.br).
# P. F. Silva, Author is with CCET, Universidade Federal de São Carlos, Brasil, (e-mail: paulofs@estudante.ufscar.br).
# P. Rossoni, Author is with CECS, Federal University of ABC, Santo André, Brasil, (e-mail: priscila.rossoni@ufabc.edu.br).
#
# This code can be used to perform maximum loadability analysis of the network using TCSC allocation and 
# studies related to TCSC adjustments for different objectives.
#
# To solve the problem, Knitro can be used as well as other solvers. Due to the non-linear and non-convex
# characteristic of the problem, the adjustment of the parameters of the solvers can lead to different solutions, 
# as well as the adjustment of the limits of the variables and constraints.

reset;
#------------------------------------------------------------------------------------------------------------------------------------------------
set BUS;    # set of buses
set BRANCH within {1..300} cross BUS cross BUS; # set of branches

#-------------------------------------------------------------------------------------------------------------------------------------------------
# PARAMETERS 

param w1;
param w2;
param w3;

# Adjusted based on the objectives.

let w1:=1;
let w2:=0;
let w3:=0;

# bus data

param bus_type       {BUS}; 
param bus_name       {BUS} symbolic;
param bus_volt0   {BUS};
param bus_angle0     {BUS};
param bus_p_gen      {BUS};
param bus_q_gen      {BUS};
param bus_q_min      {BUS};
param bus_q_max      {BUS};
param bus_p_l        {BUS};
param bus_q_l        {BUS};
param bus_g_shunt    {BUS};
param bus_b_shunt    {BUS};
param bus_p_gen_max  {BUS};


# branch data

param branch_type      {BRANCH};
param branch_r         {BRANCH};
param branch_x         {BRANCH};
param branch_c         {BRANCH};
param branch_tap0      {BRANCH};
param branch_tap_min  {BRANCH};
param branch_tap_max  {BRANCH};
param branch_def       {BRANCH};
param branch_def_min   {BRANCH};
param branch_def_max   {BRANCH};
#param branch_tcsc  {BRANCH};
param branch_xtcsc0    {BRANCH};
param branch_Sth       {BRANCH};
param branch_xtcsc_min {(l,k,m) in BRANCH} :=-branch_x[l,k,m]*0.7;
param branch_xtcsc_max {(l,k,m) in BRANCH} := branch_x[l,k,m]*0.2;

#-------------------------------------------------------------------------------------------------------------------------------------------------
# VARIABLES
# To be determined through optimization

var bus_volt  {i in BUS} >= 0.94, <= 1.06; # Adjusted based on the objectives.
var bus_angle    {i in BUS};
var branch_tap   {(l,k,m) in BRANCH} >= branch_tap_min[l,k,m], <= branch_tap_max[l,k,m]; 
var overload     >=1; # Adjusted based on the objectives.
var bus_p_load   {i in BUS} = overload*bus_p_l[i];
var bus_q_load   {i in BUS} = overload*bus_q_l[i];
var branch_tcsc {(l,k,m) in BRANCH} >=0 binary;
var branch_xtcsc    {(l,k,m) in BRANCH} >= branch_xtcsc_min[l,k,m], <= branch_xtcsc_max[l,k,m]; 
var branch_g         {(l,k,m) in BRANCH} =  branch_r[l,k,m]/(branch_r[l,k,m]^2+(branch_x[l,k,m]+(branch_xtcsc[l,k,m])*branch_tcsc[l,k,m])^2);
var branch_b         {(l,k,m) in BRANCH} = -(branch_x[l,k,m]+(branch_xtcsc[l,k,m]*branch_tcsc[l,k,m]))/(branch_r[l,k,m]^2+(branch_x[l,k,m]+(branch_xtcsc[l,k,m]*branch_tcsc[l,k,m]))^2);

# Auxiliar variables

var p_g {BUS}; # final active power generation, used to output data
var q_g {BUS}; # final reactive power generation, used to output data
var q_d {BRANCH}; # final reactive direct flow, used to output data
var q_r {BRANCH}; # final reactive reverse flow, used to output data
var p_d {BRANCH}; # final active direct flow, used to output data
var p_r {BRANCH}; # final active reverse flow, used to output data
var s_d {BRANCH}; # final aparent direct flow, used to output data
var s_r {BRANCH}; # final aparent reverse flow, used to output data

#-------------------------------------------------------------------------------------------------------------------------------------------------
# Matrix YBUS

set YBUS := setof{i in BUS} (i,i) union 
setof {(l,k,m) in BRANCH} (k,m) union
setof {(l,k,m) in BRANCH} (m,k);

var G{(k,m) in YBUS} =
if(k == m) then (bus_g_shunt[k] + sum{(l,k,i) in BRANCH} branch_g[l,k,i]*branch_tap[l,k,i]^2
                                + sum{(l,i,k) in BRANCH} branch_g[l,i,k])
else if(k != m) then (sum{(l,k,m) in BRANCH} (-branch_g[l,k,m]*cos(branch_def[l,k,m])-branch_b[l,k,m]*sin(branch_def[l,k,m]))*branch_tap[l,k,m]
                     +sum{(l,m,k) in BRANCH} (-branch_g[l,m,k]*cos(branch_def[l,m,k])+branch_b[l,m,k]*sin(branch_def[l,m,k]))*branch_tap[l,m,k]);
 
var B{(k,m) in YBUS} =
if(k == m) then (bus_b_shunt[k] + sum{(l,k,i) in BRANCH} (branch_b[l,k,i]*branch_tap[l,k,i]^2 + branch_c[l,k,i]/2)
                                + sum{(l,i,k) in BRANCH} (branch_b[l,i,k]+branch_c[l,i,k]/2))
else if(k != m) then (sum{(l,k,m) in BRANCH} (branch_g[l,k,m]*sin(branch_def[l,k,m])-branch_b[l,k,m]*cos(branch_def[l,k,m]))*branch_tap[l,k,m]
                     +sum{(l,m,k) in BRANCH} (-branch_g[l,m,k]*sin(branch_def[l,m,k])-branch_b[l,m,k]*cos(branch_def[l,m,k]))*branch_tap[l,m,k]);

# important information

var reactive_generation =  sum {k in BUS} abs(bus_q_load[k] + sum{(k,m) in YBUS} (bus_volt[k]*bus_volt[m]*
                          (G[k,m]*sin(bus_angle[k]-bus_angle[m])-B[k,m]*cos(bus_angle[k]-bus_angle[m]))));

var inductive_generation =  sum {k in BUS} min(bus_q_load[k] + sum{(k,m) in YBUS} (bus_volt[k]*bus_volt[m]*
                          (G[k,m]*sin(bus_angle[k]-bus_angle[m])-B[k,m]*cos(bus_angle[k]-bus_angle[m]))),0);

var capacitive_generation =  sum {k in BUS} max(bus_q_load[k] + sum{(k,m) in YBUS} (bus_volt[k]*bus_volt[m]*
                          (G[k,m]*sin(bus_angle[k]-bus_angle[m])-B[k,m]*cos(bus_angle[k]-bus_angle[m]))),0);


# OBJECTIVES - linear expression in the parameters and variables
#-------------------------------------------------------------------------------------------------------------------------------------------------

maximize func_obj: 	w1*sum {k in BUS} (bus_p_load[k])
		       +w2*sum {k in BUS} (1 - bus_volt[k])^2
		       +w3*sum {(l,k,m) in BRANCH} (branch_g[l,k,m]*(bus_volt[k]^2*branch_tap[l,k,m]^2 + bus_volt[m]^2
                        -2*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*cos(bus_angle[k]-bus_angle[m]))); 
			                       
# CONSTRAINTS - Linear equality or inequality in the parameters and variables
#-------------------------------------------------------------------------------------------------------------------------------------------------

subject to p_load {k in BUS : bus_type[k] == 0 || bus_type[k] == 2}:
   bus_p_gen[k] - bus_p_load[k] - sum{(k,m) in YBUS} (bus_volt[k]*bus_volt[m]*
                          (G[k,m]*cos(bus_angle[k]-bus_angle[m])+B[k,m]*sin(bus_angle[k]-bus_angle[m]))) = 0;

subject to q_load {k in BUS : bus_type[k] == 0}:
   bus_q_gen[k] - bus_q_load[k] - sum{(k,m) in YBUS} (bus_volt[k]*bus_volt[m]*
                          (G[k,m]*sin(bus_angle[k]-bus_angle[m])-B[k,m]*cos(bus_angle[k]-bus_angle[m]))) = 0;

subject to q_inj {k in BUS : bus_type[k] == 2 || bus_type[k] == 3}:
   bus_q_min[k] <= bus_q_load[k] + sum{(k,m) in YBUS} (bus_volt[k]*bus_volt[m]*
                        (G[k,m]*sin(bus_angle[k]-bus_angle[m])-B[k,m]*cos(bus_angle[k]-bus_angle[m]))) <= bus_q_max[k];
                        
subject to p_inj {k in BUS : bus_type[k] == 3}:
   0 <= bus_p_load[k] + sum{(k,m) in YBUS} (bus_volt[k]*bus_volt[m]*
               (G[k,m]*cos(bus_angle[k]-bus_angle[m])+B[k,m]*sin(bus_angle[k]-bus_angle[m]))) <= bus_p_gen_max[k];                        
             
# Line thermal limit
subject to w_d {(l,k,m) in BRANCH}:
-branch_Sth[l,k,m] <= branch_g[l,k,m]*bus_volt[k]^2*branch_tap[l,k,m]^2 
-branch_g[l,k,m]*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*cos(bus_angle[k]-bus_angle[m]+branch_def[l,k,m])
-branch_b[l,k,m]*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*sin(bus_angle[k]-bus_angle[m]+branch_def[l,k,m]) <= branch_Sth[l,k,m];

subject to w_r {(l,k,m) in BRANCH}:
-branch_Sth[l,k,m] <= branch_g[l,k,m]*bus_volt[m]^2 
-branch_g[l,k,m]*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*cos(bus_angle[k]-bus_angle[m]+branch_def[l,k,m])
+branch_b[l,k,m]*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*sin(bus_angle[k]-bus_angle[m]+branch_def[l,k,m]) <= branch_Sth[l,k,m];



#---------------------------------------------------------
subject to MAXdispatch: sum {(l,k,m) in BRANCH} branch_tcsc[l,k,m] <= 2;  # "<= 0" Adjusted based on the objectives.
#---------------------------------------------------------
var num_tcsc = sum {(l,k,m) in BRANCH} branch_tcsc[l,k,m];


# DATA - AMPL hasread and processed the contents
#-------------------------------------------------------------------------------------------------------------------------------------------------
data;

param: BUS: bus_type bus_name bus_volt0 bus_angle0 bus_p_gen bus_q_gen
            bus_q_min bus_q_max bus_p_l bus_q_l bus_g_shunt bus_b_shunt
            bus_p_gen_max:= 
include  IEEE118.bus;

param: BRANCH: branch_type branch_r branch_x branch_c
               branch_tap0 branch_tap_min branch_tap_max 
               branch_def branch_def_min branch_def_max
               branch_tcsc branch_xtcsc0 branch_Sth :=
include  IEEE118_th_lim.branch;


# data scaling and initialization

for{i in BUS} {
   let bus_volt[i] := 1;
   let bus_angle[i] := 0;
   let bus_p_gen[i] := bus_p_gen[i]/100;
   let bus_q_gen[i] := bus_q_gen[i]/100; 
   let bus_q_min[i] := bus_q_min[i]/100;
   let bus_q_max[i] := bus_q_max[i]/100;
   let bus_p_l[i] := bus_p_l[i]/100;
   let bus_q_l[i] := bus_q_l[i]/100;
   let bus_p_gen_max[i] := bus_p_gen_max[i]/100;
  };


for{(l,k,m) in BRANCH} {
   let branch_def[l,k,m] := -branch_def[l,k,m]*3.14159/180;
   let branch_def_min[l,k,m] := branch_def_min[l,k,m]*3.14159/180;
   let branch_def_max[l,k,m] := branch_def_max[l,k,m]*3.14159/180;
   let branch_Sth[l,k,m] := branch_Sth[l,k,m]/100;
       
  };

# fixed variables

fix {i in BUS : bus_type[i] == 3} bus_angle[i]; # slack angle fixed
fix {(l,k,m) in BRANCH : branch_type[l,k,m] == 0 || branch_type[l,k,m] == 3 || branch_type[l,k,m] == 4} branch_tap[l,k,m]; # branch taps fixed

#-----------------------------------------------------------------------------------------------------------------------
#SOLVER

printf "\n Optimization solver:\n\n"; #Adjust solvers information.

option solver knitro;
option knitro_options " outlev=6 alg=1 "; #mip_selectrule=1 mip_branchrule=1  mip_pseudoinit=2 mip_method=1  mip_outinterval=1 mip_heuristic=0";
solve func_obj;
#-----------------------------------------------------------------------------------------------------------------------

# calculates both active and reactive power generation

for{k in BUS} { 
  let p_g[k]  := bus_p_load[k] + sum{(k,m) in YBUS} (bus_volt[k]*bus_volt[m]*
                 (G[k,m]*cos(bus_angle[k]-bus_angle[m])+B[k,m]*sin(bus_angle[k]-bus_angle[m])));


  let q_g[k]  := bus_q_load[k] + sum{(k,m) in YBUS} (bus_volt[k]*bus_volt[m]*
                 (G[k,m]*sin(bus_angle[k]-bus_angle[m])-B[k,m]*cos(bus_angle[k]-bus_angle[m])));
}


# calculates both active and reactive direct and reverse fluxes

for{(l,k,m) in BRANCH} {

let p_d[l,k,m] := branch_g[l,k,m]*bus_volt[k]^2*branch_tap[l,k,m]^2 
-branch_g[l,k,m]*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*cos(bus_angle[k]-bus_angle[m]+branch_def[l,k,m])
-branch_b[l,k,m]*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*sin(bus_angle[k]-bus_angle[m]+branch_def[l,k,m]);

let q_d[l,k,m] :=-(branch_b[l,k,m]+branch_c[l,k,m]/2)*bus_volt[k]^2*branch_tap[l,k,m]^2 
-branch_g[l,k,m]*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*sin(bus_angle[k]-bus_angle[m]+branch_def[l,k,m])
+branch_b[l,k,m]*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*cos(bus_angle[k]-bus_angle[m]+branch_def[l,k,m]);

let p_r[l,k,m] := branch_g[l,k,m]*bus_volt[m]^2 
-branch_g[l,k,m]*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*cos(bus_angle[k]-bus_angle[m]+branch_def[l,k,m])
+branch_b[l,k,m]*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*sin(bus_angle[k]-bus_angle[m]+branch_def[l,k,m]);

let q_r[l,k,m] :=-(branch_b[l,k,m]+branch_c[l,k,m]/2)*bus_volt[m]^2 
+branch_g[l,k,m]*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*sin(bus_angle[k]-bus_angle[m]+branch_def[l,k,m])
+branch_b[l,k,m]*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*cos(bus_angle[k]-bus_angle[m]+branch_def[l,k,m]);

let s_d[l,k,m] := (p_d[l,k,m]^2 + q_d[l,k,m]^2)^0.5;
let s_r[l,k,m] := (p_r[l,k,m]^2 + q_r[l,k,m]^2)^0.5;

}

# INFORMATIONS
var Loss = sum {(l,k,m) in BRANCH} (branch_g[l,k,m]*(bus_volt[k]^2*branch_tap[l,k,m]^2 + bus_volt[m]^2
                       -2*bus_volt[k]*bus_volt[m]*branch_tap[l,k,m]*cos(bus_angle[k]-bus_angle[m])));
var Load = sum{k in BUS} overload*bus_p_l[k];                      

#-----------------------------------------------------------------------------------------------------------------------
# generates output file
#-----------------------------------------------------------------------------------------------------------------------
printf "Number of allocated TCSCs:%8.2f\n", num_tcsc > Result.txt;
printf "Overload:%8.3f\n", overload > Result.txt;
printf "Total Voltage Deviation [pu]: %8.2f\n", sum{k in BUS} abs(bus_volt[k]-1) >> Result.txt;
printf "Total Load [MW]:%8.1f\n", Load*100 > Result.txt;
printf "Total Loss [MW]:%8.1f\n", Loss*100 > Result.txt;

printf "Total Active Generation;%8.2f MW\n", sum{k in BUS} p_g[k]*100 >> Result.txt;
printf "Total Reactive Generation:%8.2f Mvar\n", reactive_generation*100 >> Result.txt;
printf "Total Inductive Generation:%8.2f Mvar\n", inductive_generation*100 >> Result.txt;
printf "Total Capacitive Generation:%8.2f Mvar\n\n", capacitive_generation*100 >> Result.txt;
printf "BUS\n" >> Result.txt;
printf "   #     Name     Voltage  Angle    PGen     QGen   PLoad    QLoad\n" >> Result.txt;
for{i in BUS} {
printf "%4d %s %6.4f %6.2f %8.2f %8.2f %8.2f %8.2f\n", i, bus_name[i], bus_volt[i], bus_angle[i]*180/3.14159,
p_g[i]*100, q_g[i]*100, bus_p_load[i]*100, bus_q_load[i]*100 >> Result.txt;
}
printf "\nBRANCH\n" >> Result.txt;
printf " From  To   on/off(TCSC)   Xij     Xtcsc    rtcsc      p_d      q_d      s_d      p_r      q_r      s_r       Sth   \n " >> Result.txt;
for{(l,k,m) in BRANCH} {
printf "%4d %4d %6d  %13.4f %8.4f %8.4f %8.1f %8.1f %8.1f %8.1f %8.1f %8.1f %8.1f\n",k, m, branch_tcsc[l,k,m], branch_x[l,k,m]+branch_xtcsc[l,k,m], 
branch_xtcsc[l,k,m], branch_xtcsc[l,k,m]/branch_x[l,k,m], p_d[l,k,m]*100, q_d[l,k,m]*100, s_d[l,k,m]*100, 
p_r[l,k,m]*100, q_r[l,k,m]*100, s_r[l,k,m]*100, branch_Sth[l,k,m]*100 >> Result.txt;
}
#-----------------------------------------------------------------------------------------------------------------------
