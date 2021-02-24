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

//set of recharging stations
{Node} F = {n | n in Nodes: n.Type == "f"};

int numero_nodi;
int d;
int c;
int f;

int C = ...;
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

//add cloned station 
int numerocopiati = 0;
execute{
  for(var k in rK){
    numerocopiati = numerocopiati + 1;
	  for(var i in rF){
	    Opl.item(F, i).StringID = Opl.item(F, i).StringID.substring(0,3);
	    Opl.item(F, i).StringID = Opl.item(F, i).StringID + " - copia " + numerocopiati;    
	  }
  Fcloned.add(F);
  }  
}

//all the vertex
{Node} V = {n | n in Nodes: n.Type == "d"} union {n | n in Nodes: n.Type == "c"};
int v;
execute{
  V.add(Fcloned);
  
  Opl.item(D, 0).StringID = Opl.item(D, 0).StringID + "-{n+1}";
  V.add(D);
  
  v = V.size;
}

range rV = 0..v-1;

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


//-----------------------------------------

dvar boolean x[rV][rV][rK];
dvar boolean y[rV][rK];
dvar float+ l[rV][rK];
dvar float Obj;
//per STE


minimize Obj;
subject to
{
  
  Objective: Obj == sum(k in rK)sum(i in rV, j in rV: i!=j && i!=v-1 && j!=0)(dist[i][j]*x[i][j][k]);
  
  //Every customer assigned to a single vehicle
  forall(i in rV){
    if(i in 1..6){
      VehAss: sum(k in rK)(y[i][k]) == 1;
    }
  }
  
  //Every customer has a successor node
  forall(i in rV, k in rK){
    if(i in 1..6){
      SuccNode: sum(j in rV: j!=0 && j!=i)(x[i][j][k]) == y[i][k];
    }
  }
  
  //Flow continuity
  forall(k in rK, i in rV){
    if(i in 1..18){
      FlowCont: sum(j in rV: i!=j && j!=0)x[i][j][k] - sum(j in rV: j!=i && j!=0)x[j][i][k] == 0;
    }
  }
  
  //Eache station cloned visited at most once
  forall(j in rV){
    if(j in 7..18){
      VisitClone: sum(k in rK)sum(i in rV: i!=j && i!=v-1)x[i][j][k] <=1;
    }
  }
  
  //Each vehicle leaves form depot only once
  forall(k in rK){
    LeaveDepot: sum(j in rV: j!=0)x[0][j][k] <=1;
  }
  
   //if a vehicle leaves the depot it must return
  forall(k in rK){
    Return: sum(j in rV: j!=0)x[0][j][k] - sum(i in rV: i!= v-1)x[i][v-1][k] == 0;
  }
  
  //load on vehicles at arrival at a node lik <= C
  forall(k in rK, i in rV){
  	if(i in 1..6){
  	upperBoundLoad:  l[i][k] <= C;
  	}
  }
  
  //load on vehicles at arrival at a node lik >= Li
  forall(k in rK, i in rV){
  	if(i in 1..6){
  	lowerBoundLoad: l[i][k] >= demand[i];
  	}
  }
  
  //load constraints
  forall(k in rK, i in rV, j in rV){
  	if(i!=j && i != v-1 && j != 0){
  		loadConstraints: l[j][k] <= l[i][k] - demand[i]*x[i][j][k] - C*(1-x[i][j][k]);
  	}	
  }

  //Subtour elimination;
 // forall(i in NodesP, j in NodesP, v in rK: i!=j && Q[i]+Q[j]<=VCap[v])  
 // SE: U[i][v] - U[j][v] + VCap[v] * x[i][j][v] <= VCap[v] -Q[j];
 
}













