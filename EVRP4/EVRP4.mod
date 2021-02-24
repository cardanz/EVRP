/* The Vehicle Routing Problem (VRP)
Common capacity model
*/
 
 // definition of node
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
// set of customers
{Node} N = {n | n in Nodes: n.Type == "c"};

// depot
{Node}D = {n | n in Nodes: n.Type == "d"};

// set of customers including depot
{Node} N0 = {n | n in Nodes: n.Type == "d"} union {n | n in Nodes: n.Type == "c"};

// set of recharging stations
{Node} F = {n | n in Nodes: n.Type == "f"};

// all the node ,depot, customer,station not F'
int numero_nodi;
// number of depots
int d;
// number of customers
int c;
//number of recharcing stations
int f;

// vehichle capacity
int C = ...;
// number of vehichles
int K = ...;



execute{
  numero_nodi = Nodes.size;
  d = D.size;
  c = N.size;
  f = F.size;
}

range rNodes = 0..(numero_nodi-1);
range rN = 0..c-1;
range rF = 0..f-1;
range rK = 0..K-1;

range provacloni = 1..2;

{Node} Fcloned;

// add cloned station 
// s0 copy 1-4, s1 copy 1-4, s7 copy 1-4
int numerocopiati = 0;
execute{
  for( var i in rF){
    numerocopiati = 0;
	  for(var k in provacloni){
	    numerocopiati = numerocopiati + 1;
	    Opl.item(F, i).StringID = Opl.item(F, i).StringID.substring(0,3);
	    Opl.item(F, i).StringID = Opl.item(F, i).StringID + " - copia " + numerocopiati;    
	  	Fcloned.add(Opl.item(F, i));
	  }
  }  
}

// all the vertex
{Node} V = {n | n in Nodes: n.Type == "d"} union {n | n in Nodes: n.Type == "c"};
int v;
execute{
  // add all the clones
  //V.add(Fcloned);
  
  // add depot (n+1) in the last position return node
  //Opl.item(D, 0).StringID = Opl.item(D, 0).StringID + "-{n+1}";
  //V.add(D);
  
  v = V.size;
}

// depot (0) - customers(N) -  cloned stations (F') - depot(n+1)
range rV = 0..v-1;

//V senza depot
range rangeV = 1..v-1;

// array element with all the demands for all nodes
int demand[rangeV];
execute{
 for(var i in rangeV){
   demand[i] = Opl.item(V, i).demand;
 }
}

//dist matrix
float dist[rV][rV];
execute{
  for(var i in rV){
	  for(var j in rV){
		   if( i == j) dist[i][j] = 0.0;
		   else
		    dist[i][j] = Opl.sqrt(Opl.pow(Opl.item(V,i).x -Opl.item(V,j).x, 2) +
		                      Opl.pow(Opl.item(V,i).y -Opl.item(V,j).y, 2));                 
		}  
	}		     
}
 

range rangeNodes =0..numero_nodi;

// customers position in V
range rangeN = 1..c;
// all the node without depots (0 && n+1)
range rangeNuF = 1..v-2;
// all the  cloned stations
range rangeFfirst = c+1..v-2;


//-----------------------------------------------------------------------

dvar float+ U[rangeV][rK];
dvar boolean x[rV][rV][rK];

dvar float Obj;

minimize Obj;
subject to 
{
Objective: Obj == sum(i in rV, j in rV: i!=j) (dist[i][j]*sum(k in rK)(x[i][j][k]));

// Apart from the depot each city must be visited only once;
forall (j in rangeN)
  Visited: sum(k in rK, i in rV: i!=j) (x[i][j][k]) == 1;
  
// Each station can be visited at most once
forall (j in rangeFfirst)
  VisitedStation: sum(k in rK, i in rV: i!=j) (x[i][j][k]) <= 1;

// If a vehicle travels to a city it must also leaves from there;
forall (i in rangeV, k in rK)
  FlowCons: sum(j in rV: j!=i) (x[i][j][k]) == sum(j in rV: j!=i)(x[j][i][k]);

//  Vehicles' capacity;
forall(k in rK)
  Capacity: sum(i in rangeV, j in rangeV: j!=i)(demand[j]*x[i][j][k]) <= C;

// Each vehicle must be used at most once;
forall(k in rK)
  Capac: sum(j in rangeV) (x[0][j][k]) <= 1;
  
  
forall(i in rangeV, k in rK){
  if(i in rangeN)
  	CargoMax: U[i][k] <= C;
  else
  	CargoMin: U[i][k] == 0;
}  

// Subtour elimination;
forall(i in rangeV, j in rangeV, k in rK: i!=j && demand[i]+demand[j]<=C)  
  SE: U[i][k] - U[j][k] + C * x[i][j][k] <= C - demand[j];
  
}