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
float maxx = 100000;
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
range NodesN0 = 0..c;

// number of node without depot or n+1
range NodesD = 1..v-2;

// number of vehicles
range Vehicles=1..K;

// range of customers
range rCustomers = 1..c;

// range of stations including the clones (3 al momento)
range rStations = c+1..v-2;

// load variables
dvar int+ U[i in rV][k in Vehicles] in demand[i]..C;

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
	    if(i != v-1 && j != 0 && i != j){
	    	M[i][j] = 0;
	    	if(dueDate[i] + serviceTime[i] + Dist[i][j]/speeds - readyTime[j] > 0 && Dist[i][j] != 0){
	      		M[i][j] = dueDate[i] + serviceTime[i] + Dist[i][j]/speeds - readyTime[j];
	      	}
     	}	      
	  } 
 	}	  
}

minimize Obj;
subject to 
{
Objective: Obj == sum(i in rV, j in rV: i!=j && i!=v-1 && j!=0) (Dist[i][j]*sum(k in Vehicles)(x[i][j][k]));

// Apart from the depot each city must be visited only once;
forall (j in rCustomers)
  VisitedCustomers: sum(k in Vehicles, i in rV: i!=j && i!= v-1) (x[i][j][k]) == 1;
  
// station visited   
forall (j in rStations)
  VisitedStations: sum(k in Vehicles, i in rV: i!=j && i!= v-1) (x[i][j][k]) <= 1;

// If a vehicle travels to a city or a station it must also leaves from there;
forall (i in NodesD, k in Vehicles)
  FlowCons: sum(j in rV: j!=i && j!= 0) (x[i][j][k]) == sum(j in rV: j!=i && j!= v-1)(x[j][i][k]);
  
//each vehicles leaves from depot only once
forall(k in Vehicles){
  LeaveDepot: sum(j in NodesD)x[0][j][k] <= 1;
  
  EnterDepot: sum(j in NodesD)x[0][j][k] - sum(i in NodesD)x[i][v-1][k] == 0;
}

//  Vehicles' capacity;
forall(k in Vehicles)
  Capacity: sum(i in rV, j in NodesD: j!=i)(demand[j]*x[i][j][k]) <= C;

// Subtour elimination;
forall(i in rV, j in rV, k in Vehicles: j != i && i!= v-1 && j!=0  && demand[i]+demand[j]<=C)  
  SE: U[j][k] - U[i][k] + C * x[i][j][k] <= C -demand[i] * x[i][j][k];
  
  
// arrival time at nodes from customers 
forall (i in NodesN0, j in rV ,k in Vehicles: i != j && j != 0)
  ArrivalTime: w[j][k] >= w[i][k] + serviceTime[i] + Dist[i][j]/speeds - M[i][j] * (1 - x[i][j][k]);
  
  // PROBLEMA: non viene visualizzato questo vincolo
  // macchina 3 arco (0,1)
  // w[1][3] >= w[0][3] + 0 + 38.079/0.67
  // w[1][3] >= 56.83
    
// arrival time at nodes from customers 
forall(i in rStations, j in rV ,k in Vehicles : i != j && j != 0)
  ArrivalTimeBattery: w[j][k] >= w[i][k] + Dist[i][j]/speeds - M[i][j] * (1 - x[i][j][k]);
  
// Time windows constraints
forall(i in rV, k in Vehicles){
  TimeWindLower: w[i][k] >= readyTime[i];
  TimeWindUpper: w[i][k] <= dueDate[i];
}  
    
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









