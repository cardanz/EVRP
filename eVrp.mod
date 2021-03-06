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

// speed, vcr
tuple speedVcr{
  int speed;
  float vcr;
}

// al the node from dataset
{Node} Nodes = ...;
// set of customers
{Node} N = {n | n in Nodes: n.Type == "c"};
// depot
{Node} D = {n | n in Nodes: n.Type == "d"};
// set of recharging stations
{Node} F = {n | n in Nodes: n.Type == "f"};
// set of velocity and consumption rate
{speedVcr} speedsVcr =...;

// number of customers
int numberOfCustomer;
// number of recharcing stations
int numberOfStation;
// number of velocity
int  numberOfVelocity;
// in order to manage the number of clones, 1 = one clone for each station, 2 ... 
int numberOfClones = 1;
// number of total vertex
int numberOfVertex;

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

execute{
  numberOfCustomer = N.size;
  numberOfStation = F.size;
  numberOfVelocity = speedsVcr.size;
}

// number of real stations
range rF = 0..numberOfStation-1;
// number of vehicles
range Vehicles = 1..K;

{Node} Fcloned;
// add cloned station 
int copies = 0;

execute{
  for( var i in rF){
    copies = 0;
	  for(var k in numberOfClones){
	    copies = copies + 1;
	    Opl.item(F, i).StringID = Opl.item(F, i).StringID.substring(0,3);
	    Opl.item(F, i).StringID = Opl.item(F, i).StringID + "_clone" + copies;    
	  	Fcloned.add(Opl.item(F, i));
	  }
  }  
}

// all the vertex afther adding cloned stations 
{Node} V = {n | n in Nodes: n.Type == "d"} union {n | n in Nodes: n.Type == "c"};
execute{
  // add all the clones
  V.add(Fcloned);
  
  // modify name of the last depot 
  // add depot (n+1) in the last position as return node
  Opl.item(D, 0).StringID = Opl.item(D, 0).StringID + "_{n+1}";
  V.add(D);
  
  // saving the num of total vertex
  numberOfVertex = V.size;
}

// layout: depot (0) - customers(N) -  cloned stations (F') - depot(n+1)
range rangeVertex = 0..numberOfVertex-1;

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

range rangeSpeeds = 0.. numberOfVelocity-1;
// velocity consumption rate (kW/km)
float vcr[rangeSpeeds];
// speeds
float speeds[rangeSpeeds];
execute{
 for(var i in rangeSpeeds){
   vcr[i] = Opl.item(speedsVcr, i).vcr;
   // Km/min
   speeds[i] = (Opl.item(speedsVcr, i).speed/60);
 }
}

// distance matrix
float Dist[rangeVertex][rangeVertex];
// in order to avoid autolinks
float maxx = 0;
execute{
  for(var i in rangeVertex){
	  for(var j in rangeVertex){
		   if( i == j){
		    // autolink in order to avoid useless paths
		   	Dist[i][j] = maxx;
		   }
		   else{
		    Dist[i][j] = Opl.sqrt(Opl.pow(Opl.item(V,i).x - Opl.item(V,j).x, 2) + Opl.pow(Opl.item(V,i).y - Opl.item(V,j).y, 2)); 
		    if(Dist[i][j] == 0){
		      // cloned stations in order to avoid useless paths clone0Station0 --> clone1Station0
		      Dist[i][j] = maxx;
		      }                        
		   }  	
	  }		     
  }
}

//--------------------------------------------------------------------------------------------------------------------------------------

// variables,constraints and optimization

// number of nodes without start depot
range rangeVertexWithoutZ = 1..numberOfVertex-1;

// number of nodes (start node + customer) 
range rangeN0 = 0..numberOfCustomer;

// number of node without depot and n+1 (all the customers and all clones )
range rangeCustomerStation = 1..numberOfVertex-2;

// range of customers
range rangeCustomers = 1..numberOfCustomer;

// range of stations including the clones 
range rangeStations = numberOfCustomer+1..numberOfVertex-2;

// load variables
dvar int+ load[i in rangeVertex][k in Vehicles] in 0..C;

// links used by vehicles variables
dvar boolean x[rangeVertex][rangeVertex][Vehicles];

// start time of service at node
dvar float+ w[rangeVertex][Vehicles];

// state of charge(SOC) at arrival at node i
dvar float+ z[rangeVertex][Vehicles];

// velocity choosen in arc (i,j) from the vector of speeds
dvar boolean velocity[rangeVertex][rangeVertex][rangeSpeeds];

// objective variable
dvar float Obj;
dvar float EnergiaCarico;
dvar float EnergiaVelocita;
dvar float Distanza;

// big B for battery 
float B = 10000;

// big-M for time window Mij = max {0, bi + Si + Tij - aj} slide(90) problem  with different speeds
// we always maximize with 100000 ( instaed of using Mij) because we have differente speeds...
float M = 100000;


minimize Obj;
subject to {
  
	Objective: Obj == EnergiaCarico + EnergiaVelocita + Distanza;
	EnergiaCarico == sum(i in rangeVertex, j in rangeVertex, k in Vehicles: i != numberOfVertex-1 && i != j && j != 0)(load[j][k] * lcr * Dist[i][j]);
	EnergiaVelocita ==  sum(i in rangeVertex, j in rangeVertex, s in rangeSpeeds: i != numberOfVertex-1 && i != j && j != 0)(Dist[i][j] * vcr[s] * velocity[i][j][s]);
	Distanza == sum(i in rangeVertex, j in rangeVertex: i!=j && i!=numberOfVertex-1 && j!=0) (Dist[i][j] * sum(k in Vehicles)(x[i][j][k]));
	
	// constraint for choose the velocity on the arc 
	forall(i in rangeVertex, j in rangeVertex: i!=j && i!=numberOfVertex-1 && j!=0){
	  chooseVelocity: sum(s in rangeSpeeds) velocity[i][j][s] == sum(k in Vehicles) x[i][j][k];
	}
	
	// Apart from the depot each city must be visited only once;
	forall (j in rangeCustomers)
	  visitAllCustomers: sum(k in Vehicles, i in rangeVertex: i!=j && i!= numberOfVertex-1) (x[i][j][k]) == 1;
	  
	// station visited   
	forall (j in rangeStations)
	  visitedStations: sum(k in Vehicles, i in rangeVertex: i!=j && i!= numberOfVertex-1) (x[i][j][k]) <= 1;
	
	// If a vehicle travels to a city or a station it must also leaves from there;
	forall (i in rangeCustomerStation, k in Vehicles)
	  flowConservation: sum(j in rangeVertex: j!=i && j!= 0) (x[i][j][k]) == sum(j in rangeVertex: j!=i && j!= numberOfVertex - 1)(x[j][i][k]);
	  
	
	forall(k in Vehicles){
	  // each vehicles leaves from depot only once
	  leaveDepot: sum(j in rangeCustomerStation)x[0][j][k] <= 1;
	  
	  // and if it exit it must return 
	  enterDepot: sum(j in rangeCustomerStation)x[0][j][k] - sum(i in rangeCustomerStation) x[i][numberOfVertex - 1][k] == 0;	  
	}
	  
	// Subtour elimination;
	forall(i in rangeVertex, j in rangeVertex, k in Vehicles: j != i && i!= numberOfVertex-1 && j!=0  && demand[i] + demand[j]<=C)  
	  SE: load[j][k] - load[i][k] + C * x[i][j][k] <= C - demand[i] * x[i][j][k];
	    
	// Arrival time at nodes from customers 
	forall (i in rangeN0, j in rangeVertex, k in Vehicles: i != j && j != 0)
	  arrivalTime: w[j][k] >= w[i][k] + serviceTime[i] + sum(s in rangeSpeeds)((Dist[i][j]/speeds[s]) * velocity[i][j][s]) - M * (1 - x[i][j][k]);
	  
	// Arrival time at nodes from stations
	forall(i in rangeStations, j in rangeVertex, k in Vehicles : i != j && j != 0)
	  arrivalTimeBattery: w[j][k] >= w[i][k] + G*(Q - z[i][k]) + sum(s in rangeSpeeds)((Dist[i][j]/speeds[s]) * velocity[i][j][s]) - M * (1 - x[i][j][k]);
	  
	// Time windows constraints
	forall(i in rangeVertex, k in Vehicles){
	  timeWindLower: w[i][k] >= readyTime[i];
	  timeWindUpper: w[i][k] <= dueDate[i];
	}  
	
	// Battery capacity dimension
	forall(i in rangeVertexWithoutZ, k in Vehicles){
	  batteryCapLower: z[i][k] >= 0;
	  batteryCapUpper: z[i][k] <= Q;
	}
	
	// Start with max battery charge
	// the battery at node 0 is the maximum
	forall(k in Vehicles)
	  batteryStart: z[0][k] == Q;
	
	// The source is the depot or a customer and the destination is a customer
	forall(i in rangeN0, j in rangeCustomerStation, k in Vehicles: i != j){
	  batteryCustomer2Customer: z[i][k] - z[j][k] >= sum(s in rangeSpeeds)(Dist[i][j] * vcr[s] * velocity[i][j][s]) + load[j][k] * lcr * Dist[i][j] - B * (1 - x[i][j][k]);
	}
	
	// The source is the depot or a customer and the destination is a charging station
	forall(i in rangeN0, j in rangeStations, k in Vehicles:  i != j){
	  batteryCustomer2Station: z[i][k] >= sum(s in rangeSpeeds)(Dist[i][j] * vcr[s] * velocity[i][j][s]) + load[j][k] * lcr * Dist[i][j] - B * (1 - x[i][j][k]);
	}
	
	// The source is a charging station and the destination is a customer
	forall(i in rangeStations, j in rangeCustomers, k in Vehicles){
		batteryStation2Customer: Q - z[j][k] >= sum(s in rangeSpeeds)(Dist[i][j]* vcr[s] * velocity[i][j][s]) + load[j][k] * lcr * Dist[i][j] - B * (1 - x[i][j][k]);
	}
	
	// The source is a charging station and the destination is the final depot
	forall(i in rangeStations, k in Vehicles){
		batteryStation2Depot: Q - z[numberOfVertex - 1][k] >= sum(s in rangeSpeeds)(Dist[i][numberOfVertex - 1] * vcr[s] * velocity[i][numberOfVertex - 1][s]) + 
								load[numberOfVertex - 1][k] * lcr * Dist[i][numberOfVertex - 1] - B * (1 - x[i][numberOfVertex - 1][k]);
	}
	
	// The source is a customer and the destination is the final depot
	forall(i in rangeCustomers, k in Vehicles){
	  batteryCustomer2Depot: z[i][k] - z[numberOfVertex - 1][k] >= sum(s in rangeSpeeds)(Dist[i][numberOfVertex - 1] * vcr[s] * velocity[i][numberOfVertex - 1][s]) + 
	  							load[numberOfVertex - 1][k] * lcr * Dist[i][numberOfVertex - 1] - B * (1 - x[i][numberOfVertex - 1][k]);
	}
}


// script that write a result.csv file
execute
{
var outFile = new IloOplOutputFile("Result.csv", false);
outFile.writeln("Objective;" + cplex.getObjValue());
outFile.writeln("Lower Bound;" + cplex.getBestObjValue());
outFile.writeln("Gap;" + cplex.getMIPRelativeGap());

// file header
outFile.writeln("Vehicle;Orig;Dest;xStart;yStart;xStop;yStop;Load;Arr_i;Arr_j;Ready;Due;Speed;Dist;Time;Z_i;Z_j;vcr");

for (var v in Vehicles){
 for (var j in rangeVertex){
   for(var i in rangeVertex){ 
    if(i!=j && x[i][j][v]>=0.999){  
      for(var s in rangeSpeeds){ 	 
       if(velocity[i][j][s]>=0.999){
   	  outFile.writeln(v,";",Opl.item(V,i).StringID,";",Opl.item(V,j).StringID,";",Opl.item(V,i).x,";",Opl.item(V,i).y,";",Opl.item(V,j).x,";",Opl.item(V,j).y,";",load[j][v],
   	  ";",w[i][v],";",w[j][v],";",readyTime[j],";",dueDate[j],";",speeds[s],";",Dist[i][j],";",Dist[i][j]/speeds[s],";",z[i][v],";",z[j][v],";",vcr[s]);
    }   	  
    }   	  
    }                        
   }      
 }
}          
outFile.close();
}







