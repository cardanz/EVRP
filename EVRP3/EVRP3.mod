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

{Node} Fcloned;

// add cloned station 
// s0 copy 1-4, s1 copy 1-4, s7 copy 1-4
int numerocopiati = 0;
execute{
  for( var i in rF){
    numerocopiati = 0;
	  for(var k in rK){
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
  V.add(Fcloned);
  
  // add depot (n+1) in the last position return node
  Opl.item(D, 0).StringID = Opl.item(D, 0).StringID + "-{n+1}";
  V.add(D);
  
  v = V.size;
}

// depot (0) - customers(N) -  cloned stations (F') - depot(n+1)
range rV = 0..v-1;

// array element with all the demands for all nodes
int demand[rV];
execute{
 for(var i in rV){
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

int prova;
execute{
  prova = prova+1;
}
//-----------------------------------------

// Xijk: for all i,j € V i != j , k € K 
dvar boolean x[rV][rV][rK];
// Yik: for all i € N, k € K
dvar boolean y[rV][rK];
// lik: for all i € N, k € K
dvar float+ l[rV][rK];
// objective function
dvar float Obj;

// customers position in V
range rangeN = 1..c;
// all the node without depots (0 && n+1)
range rangeNuF = 1..v-2;
// all the  cloned stations
range rangeFfirst = c+1..v-2;

minimize Obj;
subject to
{
  
  Objective: Obj == sum(k in rK)sum(i in rV, j in rV: i!=j && i!=v-1 && j!=0)(dist[i][j] * x[i][j][k] + l[i][k]);
  
  // Every customer assigned to a single vehicle
  forall(i in rangeN){
      VehAss: sum(k in rK)(y[i][k]) == 1;
  }
  
  // Every customer has a successor node
  forall(i in rangeN, k in rK){
      SuccNode: sum(j in rV: j!=0 && j!=i)(x[i][j][k]) == y[i][k];
  }
  
  // Flow continuity
  forall(k in rK, i in rangeNuF){
      FlowCont: sum(j in rV: i!=j && j!=0)x[i][j][k] - sum(j in rV: j!=i && j!=0)x[j][i][k] == 0;
  }
  
  //Eache station cloned visited at most once
  forall(j in rangeFfirst){
      VisitClone: sum(k in rK)sum(i in rV: i!=j && i!=v-1)x[i][j][k] <=1;
   
  }
  
  // Each vehicle leaves form depot only once
  forall(k in rK){
    LeaveDepot: sum(j in rV: j!=0)x[0][j][k] <=1;
  }
  
   // if a vehicle leaves the depot it must return
  forall(k in rK){
    Return: sum(j in rV: j!=0)x[0][j][k] - sum(i in rV: i!= v-1)x[i][v-1][k] == 0;
  }
  
  // load on vehicles at arrival at a node lik <= C && load on vehicles at arrival at a node lik >= Li
  forall(k in rK, i in rN){
  	upperBoundLoad:  l[i][k] <= C;
  	lowerBoundLoad: l[i][k] >= demand[i] * y[i][k];
  }
    
  // load constraints
  //forall(k in rK, i in rV, j in rV: i!=j && i != v-1 && j != 0){
  //		loadConstraints: l[j][k] <= l[i][k] - demand[i] * x[i][j][k] - C * (1-x[i][j][k]);
  //} 
}













