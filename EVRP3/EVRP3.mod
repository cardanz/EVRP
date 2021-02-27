/*********************************************
 * OPL Model
 * Authors: Cardano Matteo Stefano Lavaggi
 * Creation Date: 22 feb 2021 at 9:10:48
 *********************************************/
 
// StringID, Type, x, y, demand, ReadyTime, DueDate, ServiceTime 
tuple Node {
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
{Node} D = {n | n in Nodes: n.Type == "d"};
// set of recharging stations
{Node} F = {n | n in Nodes: n.Type == "f"};

// number of customers
int c;
//number of recharcing stations
int f;
// vehichle capacity
int C = ...;
// number of vehichles
int K = ...;
// Capacity of the battery [KW]
float Q = ...;
// Recharging rate (min/KW)
float G = ...;
// load consumption rate (kW/km*kg)
float lcr = ...;
// velocity consumption rate (kW/km)
float vcr = ...;
// velocity
float speeds = ...;

//transform km/h --> km/min
execute{
  speeds = (speeds/60);
}

execute{
  c = N.size;
  f = F.size;
}

// number of real stations
range rF = 0..f-1;
// number of vehicles
range Vehicles = 1..K;

{Node} Fcloned;

// add cloned station 
// s0 copy 1-4, s1 copy 1-4, s7 copy 1-4
int copies = 0;
execute{
  for( var i in rF){
    copies = 0;
	  for(var k in Vehicles){
	    copies = copies + 1;
	    Opl.item(F, i).StringID = Opl.item(F, i).StringID.substring(0,3);
	    Opl.item(F, i).StringID = Opl.item(F, i).StringID + " - copy " + copies;    
	  	Fcloned.add(Opl.item(F, i));
	  }
  }  
}

// all the vertex afther adding cloned stations 
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
range rangeVertex = 0..v-1;

// array element with all the data for all nodes 
int demand[rangeVertex];
int readyTime[rangeVertex];
int dueDate[rangeVertex];
int serviceTime[rangeVertex];
execute{
 for(var i in rangeVertex){
   demand[i] = Opl.item(V, i).demand;
   readyTime[i] = Opl.item(V, i).readyTime;
   dueDate[i] = Opl.item(V, i).dueDate;
   serviceTime[i] = Opl.item(V, i).serviceTime;
 }
}

//dist matrix
float Dist[rangeVertex][rangeVertex];
// in order to avoid autolinks
float maxx = 100000;
execute{
  for(var i in rangeVertex){
	  for(var j in rangeVertex){
		   if( i == j){
		    // autolink
		   	Dist[i][j] = maxx;
		   }
		   else{
		    Dist[i][j] = Opl.sqrt(Opl.pow(Opl.item(V,i).x -Opl.item(V,j).x, 2) + Opl.pow(Opl.item(V,i).y -Opl.item(V,j).y, 2)); 
		    if(Dist[i][j] == 0){
		      // cloned stations
		      Dist[i][j] = maxx;
		      }                        
		   }  	
	  }		     
  }
}


//constraints and optimization

// number of nodes (start node + customer) 
range rangeN0 = 0..c;

// number of node without depot and n+1 (all the customers and all clones )
range rangeCustomerStation = 1..v-2;

// range of customers
range rangeCustomers = 1..c;

// range of stations including the clones 
range rangeStations = c+1..v-2;

// load variables
dvar int+ load[i in rangeVertex][k in Vehicles] in 0..C;

// links used by vehicles variables
dvar boolean x[rangeVertex][rangeVertex][Vehicles];

// start time of service at node
dvar float+ w[rangeVertex][Vehicles];

// state of charge(SOC) at arrival at node i
dvar float+ z[rangeVertex][Vehicles];

// objective variable
dvar float Obj;

// big B for battery 
float B = 1000;

// big-M for time window Mij = max {0, bi + Si + Tij - aj} slide(90)
float M[rangeVertex][rangeVertex];
execute{
  for(var i in rangeVertex){
	  for(var j in rangeVertex){
	    if(i != v-1 && j != 0 && i != j){
	    	M[i][j] = 0;
	    	if(dueDate[i] + serviceTime[i] + Dist[i][j]/speeds - readyTime[j] > 0 && Dist[i][j] != 0){
	      		// if bi + Si + Tij - aj is greater than 0 we rewrite M[i][j]
	      		M[i][j] = dueDate[i] + serviceTime[i] + Dist[i][j]/speeds - readyTime[j];
	      	}
     	}	      
	  } 
  }	  
}

minimize Obj;
subject to {
  
	Objective: Obj == sum(i in rangeVertex,j in rangeVertex, k in Vehicles:i != v-1 && i != j && j != 0)(load[j][k]*lcr*Dist[i][j]) 
						+ sum(i in rangeVertex, j in rangeVertex,k in Vehicles: i != v-1 && i != j && j != 0)(Dist[i][j]*vcr*x[i][j][k]) 
						+  sum(i in rangeVertex, j in rangeVertex: i!=j && i!=v-1 && j!=0) (Dist[i][j]*sum(k in Vehicles)(x[i][j][k]));
	
	// Apart from the depot each city must be visited only once;
	forall (j in rangeCustomers)
	  VisitAllCustomers: sum(k in Vehicles, i in rangeVertex: i!=j && i!= v-1) (x[i][j][k]) == 1;
	  
	// station visited   
	forall (j in rangeStations)
	  VisitedStations: sum(k in Vehicles, i in rangeVertex: i!=j && i!= v-1) (x[i][j][k]) <= 1;
	
	// If a vehicle travels to a city or a station it must also leaves from there;
	forall (i in rangeCustomerStation, k in Vehicles)
	  FlowConservation: sum(j in rangeVertex: j!=i && j!= 0) (x[i][j][k]) == sum(j in rangeVertex: j!=i && j!= v-1)(x[j][i][k]);
	  
	
	forall(k in Vehicles){
	  //each vehicles leaves from depot only once
	  LeaveDepot: sum(j in rangeCustomerStation)x[0][j][k] <= 1;
	  
	  //and if it exit it must return 
	  EnterDepot: sum(j in rangeCustomerStation)x[0][j][k] - sum(i in rangeCustomerStation)x[i][v-1][k] == 0;
	  
	  // max load 
	  Capacity: sum(i in rangeVertex, j in rangeCustomerStation: j!=i)(demand[j]*x[i][j][k]) <= C;
	}
	  
	
	// Subtour elimination;
	forall(i in rangeVertex, j in rangeVertex, k in Vehicles: j != i && i!= v-1 && j!=0  && demand[i]+demand[j]<=C)  
	  SE: load[j][k] - load[i][k] + C * x[i][j][k] <= C - demand[i] * x[i][j][k];
	    
	// arrival time at nodes from customers 
	forall (i in rangeN0, j in rangeVertex ,k in Vehicles: i != j && j != 0)
	  ArrivalTime: w[j][k] >= w[i][k] + serviceTime[i] + Dist[i][j]/speeds - M[i][j] * (1 - x[i][j][k]);
	  
	// arrival time at nodes from stations
	forall(i in rangeStations, j in rangeVertex ,k in Vehicles : i != j && j != 0)
	  ArrivalTimeBattery: w[j][k] >= w[i][k] + G*(Q - z[i][k]) + Dist[i][j]/speeds - M[i][j] * (1 - x[i][j][k]);
	  
	// Time windows constraints
	forall(i in rangeVertex, k in Vehicles){
	  TimeWindLower: w[i][k] >= readyTime[i];
	  TimeWindUpper: w[i][k] <= dueDate[i];
	}  
	
	// Battery capacity dimension
	forall(i in rangeVertex, k in Vehicles){
	  BatteryCapLower: z[i][k] >= 0;
	  BatteryCapUpper: z[i][k] <= Q;
	  if(i == 0)
	  	z[i][k] == Q;
	}
	
	// the source is the depot or a customer and the destination is a customer
	forall(i in rangeN0,j in rangeCustomers, k in Vehicles: i != j && j != 0){
	  z[i][k] - z[j][k] >= Dist[i][j] * vcr * x[i][j][k] - B * (1 - x[i][j][k]);
	}
	
	// the source is the depot or a customer and the destination is a charging station
	forall(i in rangeN0,j in rangeStations, k in Vehicles:  i != j){
	  z[i][k] >= Dist[i][j] * vcr * x[i][j][k] - B * (1 - x[i][j][k]);
	}
	
	// the source is a charging station and the destination is a customer
	forall(i in rangeStations, j in rangeCustomers,k in Vehicles: i != j){
		Q - z[j][k] >= Dist[i][j] * vcr * x[i][j][k] - B * (1 - x[i][j][k]);
	}
	
	// the source is a charging station and the destination is the final depot
	forall(i in rangeStations,k in Vehicles){
		Q - z[v-1][k] >= Dist[i][v-1] * vcr * x[i][v-1][k] - B * (1 - x[i][v-1][k]);
	}
	
	// the source is a customer and the destination is the final depot
	forall(i in rangeCustomers, k in Vehicles){
	  z[i][k] - z[v-1][k] >= Dist[i][v-1] * vcr * x[i][v-1][k] - B * (1 - x[i][v-1][k]);
	}
}


// script that write a result.csv file
execute
{
var outFile = new IloOplOutputFile("Result.csv", false); 
//objective lower bound gap
outFile.writeln("Obj;"+cplex.getObjValue());
outFile.writeln("LB;"+cplex.getBestObjValue());
outFile.writeln("Gap;"+cplex.getMIPRelativeGap());

// file header
outFile.writeln("Vehicle;Orig;Dest;Dist;ArrLoadOrig;ArrLoadDest");

for (var i in rangeVertex)
{
 for (var j in rangeVertex)
 {
  if(i!=j)
   for(var v in Vehicles)
   { 
    if(x[i][j][v]>=0.999) 		
    {
   	  if(j>0 && i>0) 
   	     outFile.writeln(v,";",i,";",j,";",Dist[i][j],";",load[i][v],";",load[j][v]);
   	  else if(i==0)
   	          outFile.writeln(v,";",i,";",j,";",Dist[i][j],";0;",load[j][v]);
   	       else 
   	         outFile.writeln(v,";",i,";",j,";",Dist[i][j],";",load[i][v],";0");
    }                        
   }      
 }
}          
outFile.close();
}









