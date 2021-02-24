//definition of node
tuple Node {
  // StringID Type x y demand ReadyTime DueDate ServiceTime
  string StringID;
  string Type;
  int x;
  int y;
  int demand;
  int ReadyTime;
  int DueDate;
  int ServiceTime;
}

{Node} Nodes = ...;

//set of customers
{Node} N = {n | n in Nodes: n.Type == "c"};

//depot
{Node}D = {n | n in Nodes: n.Type == "d"};

//set of customers including depot
{Node} N0 = {n | n in Nodes: n.Type == "d"} union {n | n in Nodes: n.Type == "c"};
//{string} pippo = {n.StringID | n in Nodes: n.Type == "d"} union  {n.StringID | n in Nodes: n.Type == "c"};;

//set of recharging stations
{Node} F;

int Number_of_nodes = 10;
range rnodes = 1..Number_of_nodes;

//number of depot, stations and customers in the problem
int d = 0;
int f = 0;
int c = 0;


execute {
for(var i in rnodes){
  if (Opl.item(Nodes,i-1).Type == 'd'){ 
  	d = d+1;
  	N0.add(Opl.item(Nodes,i-1));
  	D.add(Opl.item(Nodes,i-1));
  	}
  if (Opl.item(Nodes,i-1).Type == 'f'){
    f = f+1;
    F.add(Opl.item(Nodes,i-1));
  }
  if (Opl.item(Nodes,i-1).Type == 'c'){ 
  	c = c+1;
  	N.add(Opl.item(Nodes,i-1));
  	N0.add(Opl.item(Nodes,i-1));
  	}
	                   
  }
                       
}

range rN = 1..c;


//cloned stations
{Node} Fcloned;
range dimF = 1..f;
range copies = 1..3;
int number_of_copies = 0;
int numFcloned;

execute{
  for(j in copies){
    number_of_copies = number_of_copies +1;
	  for(i in dimF){
	    Opl.item(F,i-1).StringID = Opl.item(F,i-1).StringID.substring(0, 3);
	    Opl.item(F,i-1).StringID = Opl.item(F,i-1).StringID + " - copia numero: " + number_of_copies;
	    Fcloned.add(Opl.item(F,i-1));
	  }
 	}	
 	numFcloned = Fcloned.size;  
}

range rFcloned = 1..numFcloned;

//V
{Node} V;
int numV;

execute{
  V.add(D);
  Opl.item(D, 0).StringID = Opl.item(D, 0).StringID + " - {n+1}";
  V.add(D);
  V.add(N); 
  
  //da rimettere
  //V.add(Fcloned);
  numV = V.size;
}

range rV = 1..numV;


//dist matrix
float dist[rV][rV];

execute{
  for(var i in rV){
	  for(var j in rV){
		   if( i == j) dist[i][j] = 0.0;
		   else
		    dist[i][j] = Opl.sqrt(Opl.pow(Opl.item(V,i-1).x -Opl.item(V,j-1).x, 2) +
		                      Opl.pow(Opl.item(V,i-1).y -Opl.item(V,j-1).y, 2));
		    
		   //writeln(i+" x="+Opl.item(Nodes,i-1).x+" y="+Opl.item(Nodes,i-1).y+ " "+
		   //        j+" x="+Opl.item(Nodes,j-1).x+" y="+Opl.item(Nodes,j-1).y+ " "+dist[i][j]);                   
		}  
	}		     
}



//number of veichles
int K = ...; 
range rK = 1..K;

//Battery capacity
float Q = ...;

//Vehicle load capacity
float C = ...; 

// battery consumption rate for power kW/km*kg
float lcr = ...; 

// battery recharging rate min/kW
float g = ...; 

/*
//S[i] , a[i], b[i] con  i appart. a N
int S[rV_n1];
int a[rV_n1];
int b[rV_n1];
int L[rV_n1];

execute{
  for(i in rV_n1){
    S[i] = Opl.item(V_n1,i-1).ServiceTime;
    a[i] = Opl.item(V_n1,i-1).ReadyTime;
    b[i] = Opl.item(V_n1,i-1).DueDate;
    L[i] = Opl.item(V_n1,i-1).demand;
  }
}
*/


//------------------VARIABLES--------------------------------------------
//Sequencing – used links by vehicles
dvar boolean x[1..17][1..17][rK];

//Customer – vehicle assignment
dvar boolean y[rV][rK];

//Start time of service at nodes 
dvar float+ w[rV][rK];
/*
//Load on vehicles at arrival at a node
dvar float l[i in rV_n1][rK] in L[i]..C;
*/
//State of charge at arrival at a node
dvar float+ z[rV][rK];


dvar float Obj;

minimize Obj;

subject to 
{
//Objective: Obj == sum(i in rV, j in rV: i!=j) (sum(k in rK)(x[i][j][k]));
  
Objective: Obj == sum(i in 1..17, j in 1..17: i!=j) (dist[i][j]*sum(k in rK)(x[i][j][k]));

//Every customer assigned to a single vehicle
forall(i in rV){
  //3..8 perche solo i in N
  if(i in 3..8)
  VehiAss: sum(k in rK) (y[i][k]) == 1;
}


//Every customer has a successor node
forall(i in rV, k in rK ){
  //3..8 perche solo i in N
  if(i in 3..17)  
  //j!=1 perche considero il deposito come 1 e il vincolo dice j in V\ {0,i}
  Succ: sum(j in 1..17: i!=j && j!=1) (x[i][j][k]) == (y[i][k]);
}

//Every customer has a successor node
forall(k in rK ){
  SuccLast: sum(j in rV) (x[2][j][k]) == 0;
}

//Flow continuity for vehicles
forall(k in rK, j in rV){
  //3..17 perche i in N unito a F' quindi solo customer e F clonati
  if(j in 3..17)
  //somma su A ovvero insieme di archi definito in V con i!=j e i non è n+1 (per me n+1 è il 2) e j non è il deposito
  //FlowCon: sum( j in 1..17: i!=j && j!=1)(x[i][j][k]) - sum(j in 1..17 : i!=j && i!=2 )(x[j][i][k]) == 0;
  FlowCon: sum( i in 1..17: i!=j && i!=2)(x[i][j][k]) == (y[j][k]);
}

//Each station clone visited at most once
forall(j in rV){
  //j solo in F'
  if(j in 9..17)
  //somma su k e somma su A
  VisitStat: sum(k in rK, i in 1..17 : i!=j && i!=2 )(x[i][j][k]) <= 1;
}

//Each station clone visited at most once
forall(j in rV,k in rK){
  //j solo in F'
  if(j in 9..17)
  //somma su k e somma su A
  VisitStat2: sum(i in 1..17 : i!=j && i!=2 )(x[i][j][k]) == sum( i in 1..17 : i!=j && i!=1 )(x[j][i][k]);
}

//Each vehicle leaves from depot only once
forall(k in rK){
  //somma su A dove i = 1 ovvero il deposito
  VehStart: sum( j in rV:  j!=1)(x[1][j][k]) <= 1;
}

//If a vehile leaves the depot it finally return to depot
forall(k in rK){
  sum( j in rV: j!=1 )(x[1][j][k]) - sum(i in rV:  i!=2 )(x[i][2][k]) == 0;
  
}









/*

/*
//Arrival time at nodes from customers
//ATTENTO ho usato d[i][j] al posto di T[i][j] che dovrebbe essere dist/vel
forall(k in rK, i in rV_n1, j in rV_n1: i!=j && i in rN){
  Time: w[j][k] >= w[i][k] + S[i] + dist[i][j] - 10000*(1- x[i][j][k]);
}


//Arrival time at nodes from station
forall(k in rK, i in rFcloned, j in rV_n1: i!=j){
  w[j][k] >= w[i][k] + g*(Q - z[i][k]) + dist[i][j] - 10000*(1- x[i][j][k]);
}

//Time windows constraints
forall(k in rK, i in rN){
  TWlb: a[i] <= w[i][k];
  TWup: w[i][k] <= b[i];
}
*/
/*
//Veichle load contraints -------------------------------------NO VALUE
forall(k in rK, i in rV_n1, j in rV_n1: i!=j){
  l[j][k] <= l[i][k] + L[i]*x[i][j][k] - C * (1 - x[i][j][k]);
}

//SOC on arrivals from customers
forall(k in rK, i in rN, j in rV_n1: i!=j){
	z[j][k] <= z[i][k] - lcr*dist[i][j]*x[i][j][k] - 10000 * (1 - x[i][j][k]);
}

//SOC on arrivals from customers
forall(k in rK, i in rFcloned, j in rV_n1: i!=j){
	z[j][k] <= Q - lcr*dist[i][j]*x[i][j][k] - 10000 * (1 - x[i][j][k]);
}
*/
/*
//SOC bounds
forall(k in rK, i in rV){
  SOCub: z[i][k] <= Q;
}
*/
//load bounds
//forall(k in rK, i in rV_n1){
//  L[i] <= l[i][k] <= C;
//}

//service time bound
//forall(k in rK, i in rV){
//  w[i][k] >= 0;
//}

}








