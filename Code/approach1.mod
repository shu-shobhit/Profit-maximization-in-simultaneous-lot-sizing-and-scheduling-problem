/*********************************************
 * OPL 22.1.1.0 Model
 * Author: bajpa
 * Creation Date: 1 Apr 2024 at 18:15:39
 *********************************************/
int no_of_periods = ...;              			// time_periods
range time_periods = 1..no_of_periods;          
int P = ...;              						// no. of products
range products = 1..P;           
float r[products][time_periods] = ...;      // r[j][t] = sales revenue for one unit of product j in period t
int Ld[products][time_periods] = ...;       // Ld[j][t] = lower bound of demand of product j in period t
int Ud[products][time_periods] = ...;       // Ud[j][t] = upper bound of demand of product j in period t
int I0[products] = ...;          // I0[j] = initial inventory level for product j
int C[time_periods] = ...;           // C[t] = available capacity in each period
float Cp[products] = ...;        // Cp[j] = Production cost for one unit of product j
float Pt[products] = ...;        // Pt[j] = processing time_periods for one unit of product j
float h[products] = ...;         // h[j] = holding cost for one unit of product j
int s[products][products] = ...;        // s[i][j] = setup cost for transition from product i to product j
float St[products][products] = ...;     // St[i][j] = setup time_periods for transition from product i to product j
dvar int+ Q[products][time_periods]; //Q[j][t] = Production quantity of product j in period t to fulfil the demand of period t.
dvar int+ D[products][time_periods];       //D[j][t] = The accepted demand of product j in period t.
dvar int+ A[products][time_periods];       //A[j][t] = Positive variable which is 1 when machine is setup for product j at the beginning of period t.
dvar int+ Y[products][time_periods];       //Y[j][t] = Auxiliary variable that assign product j to period t.
dvar int+ I[products][time_periods];	//I[j][t] = Inventory remaining after time period t for product j.
dvar boolean X[products][products][time_periods];  //X[i][j][t] = Binary variable which is 1 when setup occur from product i to product j in period t.
dvar float+ M[products][time_periods];

//Objective Function
dexpr float z = sum(j in products, t in time_periods) r[j][t] * D[j][t] - sum(j in products, t in time_periods) Cp[j] * Q[j][t] - 
sum(j in products, i in products, t in time_periods) s[i][j] * X[i][j][t] - sum(j in products, t in time_periods)h[j]*I[j][t] ;
//The objective function maximizes total revenue minus production, setup, and inventory costs.
maximize z;

subject to
{
	Constraint_1://inventory balance constraint
	
	forall(j in products,t in time_periods)
	{
	if(t!=1)
	{
		I[j][t]==I[j][t-1]+Q[j][t]-D[j][t];
	}
	else
	{
	  I[j][t]==I0[j]+Q[j][t]-D[j][t];
	}
	
	}	
	  
	
    
	Constraint_2:
    forall(j in products, t in time_periods) D[j][t] <= Ud[j][t];//Upper Bound of demand.

    forall(j in products, t in time_periods) D[j][t] >= Ld[j][t];//Lower Bound of demand.


	Constraint_3://guarantees that a product is produced if the machine has been setup for it.
    forall(j in products, t in time_periods)
    {
		Q[j][t] <= M[j][t] * (sum(i in products) X[i][j][t] + A[j][t]);
	}		

	
	Constraint_4://shows the capacity limit for production
    forall(t in time_periods) sum(j in products) Pt[j] * Q[j][t] + sum(i in products, j in products) St[i][j] * X[i][j][t] <= C[t];

	//Upper bound for the quantity of production in constraint
    forall(j in products, t in time_periods) 
    if (C[t] / Pt[j] < sum(k in t..no_of_periods)Ud[j][k]) 
    {
    	M[j][t] == C[t] / Pt[j];
  	}    
    else
    {
        M[j][t] == sum(k in t..no_of_periods)Ud[j][k];
    }
    
    
	Constraint_5://shows that at the beginning of each period there is only one setup state.
    forall(t in time_periods) sum(j in products) A[j][t] == 1;

    
    Constraint_6:// guarantee that the setup states network is a connected network 
    forall(j in products, t in 1..(no_of_periods-1))
    { 
   
    	A[j][t] + sum(i in products) X[i][j][t] == A[j][t + 1] + sum(i in products) X[j][i][t]; 
    
    }
    
    
	Constraint_7://avoid disconnected sub tours.
    forall(i in products, j in products, t in time_periods: i!=j)
    { 
  		Y[i][t] + P*X[i][j][t] - (P - 1) - P *A[i][t] <= Y[j][t]; 
    }

    
}

