// definition of node
tuple Node {
  // StringID Type x y demand ReadyTime DueDate ServiceTime
  string StringID;
  string Type;
  int x;
  int y;
  int demand;
  int readyTime;
  int dueDate;
  int serviceTime;
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

//velocity
float speeds = ...;
// km/min
execute{
  speeds = (speeds/60);
}

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

// array element with all the data for all nodes 
int demand[rV];
int readyTime[rV];
int dueDate[rV];
int serviceTime[rV];
execute{
 for(var i in rV){
   demand[i] = Opl.item(V, i).demand;
   readyTime[i] = Opl.item(V, i).readyTime;
   dueDate[i] = Opl.item(V, i).dueDate;
   serviceTime[i] = Opl.item(V, i).serviceTime;
 }
}

//dist matrix
float Dist[rV][rV];
float maxx = 100000.0;
execute{
  for(var i in rV){
	  for(var j in rV){
		   if( i == j){
		   	Dist[i][j] = maxx;
		   }
		   else{
		    Dist[i][j] = Opl.sqrt(Opl.pow(Opl.item(V,i).x -Opl.item(V,j).x, 2) +
		    	Opl.pow(Opl.item(V,i).y -Opl.item(V,j).y, 2)); 
		    if(Dist[i][j] == 0){
		      Dist[i][j] = maxx;
		      }                        
		   }  	
	 }		     
  }
}


//-----------------------------------------

// number of nodes without depot 
range NodesP = 1..v-1;

// number of vehicles
range Vehicles=1..K;

// range of customers
range rCustomers = 1..c;

// range of stations including the clones (3 al momento)
range rStations = c+1..v-1;

// load variables
dvar int+ U[i in NodesP][v in Vehicles] in demand[i]..C;

// links used by vehicles variables
dvar boolean x[rV][rV][Vehicles];

// start time of service at node
dvar float+ w[rV][Vehicles];

// objective variable
dvar float Obj;

// big-M for time window
float M[rV][rV];
execute{
  for(var i in rV){
	  for(var j in rV){
	    M[i][j] = 0;
	    if(dueDate[i] + serviceTime[i] + Dist[i][j]/speeds - readyTime[j] > 0){
	      M[i][j] = dueDate[i] + serviceTime[i] + Dist[i][j]/speeds - readyTime[j];
	      }
	  } 
  }
}

minimize Obj;
subject to 
{
Objective: Obj == sum(i in NodesP, v in Vehicles)U[i][v] + sum(i in rV, j in rV: i!=j) (Dist[i][j]*sum(v in Vehicles)(x[i][j][v]));

// Apart from the depot each city must be visited only once;
forall (j in rCustomers)
  VisitedCustomers: sum(v in Vehicles, i in rV: i!=j) (x[i][j][v]) == 1;
  
// station visite   
forall (j in rStations)
  VisitedStations: sum(v in Vehicles, i in rV: i!=j) (x[i][j][v]) <= 1;

// If a vehicle travels to a city it must also leaves from there;
forall (i in NodesP, v in Vehicles)
  FlowCons: sum(j in rV: j!=i) (x[i][j][v]) == sum(j in rV: j!=i)(x[j][i][v]);

//  Vehicles' capacity;
forall(v in Vehicles)
  Capacity: sum(i in rV, j in NodesP: j!=i)(demand[j]*x[i][j][v]) <= C;

// Each vehicle must be used at most once;
forall(v in Vehicles)
  Capac: sum(j in NodesP) (x[0][j][v]) <= 1;

// Subtour elimination;
forall(i in NodesP, j in NodesP, v in Vehicles: i!=j && demand[i]+demand[j]<=C)  
  SE: U[j][v] - U[i][v] + C * x[i][j][v] <= C -demand[i];
  
  
// arrival time at nodes from customers 
forall(v in Vehicles, i in rCustomers, j in rV : i != j)
  ArrivalTime: w[j][v] >= w[i][v] + serviceTime[i] + Dist[i][j]/speeds - M[i][j] * (1 - x[i][j][v]);
    
// arrival time at nodes from customers 
forall(v in Vehicles, i in rStations, j in rV : i != j)
  ArrivalTimeBattery: w[j][v] >= w[i][v] + Dist[i][j]/speeds - M[i][j] * (1 - x[i][j][v]);
    
}




// script that write a result.csv file
execute
{
var outFile = new IloOplOutputFile("Risult.csv", false); 
//objective lower bound gap
outFile.writeln("Obj;"+cplex.getObjValue());
outFile.writeln("LB;"+cplex.getBestObjValue());
outFile.writeln("Gap;"+cplex.getMIPRelativeGap());

// file header
outFile.writeln("Vehicle;Orig;Dest;Dist;ArrLoadOrig;ArrLoadDest");

for (var i in rV)
{
 for (var j in rV)
 {
  if(i!=j)
   for(var v in Vehicles)
   { 
    if(x[i][j][v]>=0.999) 		
    {
   	  if(j>0 && i>0) 
   	     outFile.writeln(v,";",i,";",j,";",Dist[i][j],";",U[i][v],";",U[j][v]);
   	  else if(i==0)
   	          outFile.writeln(v,";",i,";",j,";",Dist[i][j],";0;",U[j][v]);
   	       else 
   	         outFile.writeln(v,";",i,";",j,";",Dist[i][j],";",U[i][v],";0");
    }                        
   }      
 }
}          
outFile.close();
}









