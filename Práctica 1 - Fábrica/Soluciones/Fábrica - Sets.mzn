%numero de trabajadores
int: T;

%numero de dias
int: D; 

%numero de dias consecutivos que puede trabajar un empleado
int: MaxDT;

%numero de dias consecutivos que puede librar un empleado
int: MaxDL;

%numero mínimo de días trabajados por trabajador en los D días.
int: MinDT;

%numero de trabajadores cada turno
int: N1;
int: N2;
int: N3;

%Afinidad entre trabajadores
array[1..T, 1..T] of int: Afinidad;
int: A;

%Turnos de los trabajadores
enum Turnos = {T1, T2, T3, L1};
array[1..3,1..D] of var set of 1..T: sol;
array[1..D] of var set of 1..T: TrabajadoresDia;

%Categorías de los trabajadores.
int: C;
array[1..T] of 1..C: Categorias;
array[1..3*C] of int: MinTC;

%Matriz de días libres.
array[1..T,1..D] of bool: DiasLibres;

%Matriz de turnos no deseados.
array[1..T,1..D] of Turnos: TurnosNoDeseados;

%Asserts
constraint assert(D > 0, "Los días a organizar deben ser mayor que 0.");
constraint assert(T > N1 + N2 + N3, "No hay trabajadores suficientes para todos los turnos de un día.");
constraint assert(N1 > A /\ N2 > A /\ N3 > A, "Algún turno necesita más trabajadores para poder cumplir la restricción de afinidad.");
constraint forall(c in 1..C, t in 1..3)(assert(sum(j in 1..T)(Categorias[j] = c) > MinTC[C*(t-1) + c], "No hay suficientes trabajadores de la categoría \(c) para los turnos \(t)."));

%Variable auxiliar.
constraint forall(i in 1..D)(TrabajadoresDia[i] = sol[1,i] union sol[2,i] union sol[3,i]);

%Cada turno tiene el número de trabajadores (N1, N2 o N3) que le corresponde.
constraint forall(i in 1..D)(card(sol[1,i]) = N1 /\ card(sol[2,i]) = N2 /\ card(sol[3,i]) = N3);

%Un trabajador solo puede trabajar un turno cada día.
constraint forall(i in 1..D, t1 in 1..3, t2 in 1..3 where t1 != t2)(sol[t1,i] intersect sol[t2,i] = {});

%Un trabajador no trabaja MaxDT días seguidos.
constraint forall(i in 1..D - (MaxDT - 1))(array_intersect(TrabajadoresDia[i..i + (MaxDT - 1)]) = {});

%Un trabajador no libra MaxDL días seguidos. (Los días libres que se pide cuentan como trabajados).
constraint forall(i in 1..T, j in 1..D - (MaxDL - 1))(sum(k in j..j + (MaxDL - 1))(bool2int((not (i in TrabajadoresDia[k])) /\ not DiasLibres[i,k])) < MaxDL);

%Un trabajador trabaja como mínimo MinDT días. (Los días libres que se pide cuentan como trabajados).
constraint forall(i in 1..T)(sum(j in 1..D)(bool2int((i in TrabajadoresDia[j]) \/ DiasLibres[i,j])) >= MinDT);

%Un trabajador no puede hacer el último turno de un día y el primero del día siguiente dos veces consecutivas.
constraint forall(i in 1..T, j in 1..D - 3)((i in sol[3,j] /\ i in sol[1,j + 1] /\ i in sol[3,j + 2]) -> not (i in sol[1,j + 3]));

%Cada trabajador trabaja con al menos A trabajadores afines en su turno.
constraint forall(i in 1..D, j in 1..T where j in TrabajadoresDia[i])(sum(k in 1..T where j != k /\ (j in sol[1, i] /\ k in sol[1, i]) \/ (j in sol[2, i] /\ k in sol[2, i]) \/ (j in sol[3, i] /\ k in sol[3, i]))(Afinidad[j,k]) >= A);
%constraint forall (i in 1..D, turno in 1..3)  (sum (t in sol[turno,i], t1 in sol[turno,i]) (Afinidad[t,t1]) >= A );

%En cada turno hay mínimo un trbajador de cada categoría.
constraint forall(i in 1..D, c in 1..C)(sum(j in 1..T)(bool2int(j in sol[1, i] /\ Categorias[j] = c)) >= MinTC[c]);
constraint forall(i in 1..D, c in 1..C)(sum(j in 1..T)(bool2int(j in sol[2, i] /\ Categorias[j] = c)) >= MinTC[C*1 + c]);
constraint forall(i in 1..D, c in 1..C)(sum(j in 1..T)(bool2int(j in sol[3, i] /\ Categorias[j] = c)) >= MinTC[C*2 + c]);

/***************PROBLEMA DE SATISFACCIÓN***************/

%Los trabajadores no trabajan los turnos que han pedido no trabajar.
%constraint forall(i in 1..T, j in 1..D)((TurnosNoDeseados[i,j] = T1) -> (not (i in sol[1,j])));
%constraint forall(i in 1..T, j in 1..D)((TurnosNoDeseados[i,j] = T2) -> (not (i in sol[2,j])));
%constraint forall(i in 1..T, j in 1..D)((TurnosNoDeseados[i,j] = T3) -> (not (i in sol[3,j])));

%Los trabajadores libran los días que han pedido.
%constraint forall(i in 1..T, j in 1..D)(DiasLibres[i,j] -> not (i in TrabajadoresDia[j]));

%solve satisfy;

/******************************************************/







/***************PROBLEMA DE OPTIMIZACIÓN***************/

%Minimiza el número de días libres pedidos no concedidos.
%solve minimize sum(i in 1..D, j in 1..T)(bool2int(DiasLibres[j,i] /\ j in TrabajadoresDia[i]));

%Minimiza el número de turnos no deseados pedidos no concedidos.
%solve minimize sum(i in 1..D, j in 1..T)(bool2int((TurnosNoDeseados[j,i] = T1 /\ j in sol[1,i]) \/ (TurnosNoDeseados[j,i] = T2 /\ j in sol[2,i]) \/ (TurnosNoDeseados[j,i] = T3 /\ j in sol[3,i])) );

%Minimiza el número de días libres pedidos y turnos no deseados no concedidos.
solve minimize sum(i in 1..D, j in 1..T)(bool2int(DiasLibres[j,i] /\ j in TrabajadoresDia[i]) + bool2int((TurnosNoDeseados[j,i] = T1 /\ j in sol[1,i]) \/ (TurnosNoDeseados[j,i] = T2 /\ j in sol[2,i]) \/ (TurnosNoDeseados[j,i] = T3 /\ j in sol[3,i])));

/******************************************************/







/******************SOLUCIÓN****************************/
output [ "\(sol[i,j])" ++ 
         if j == D then "\n" else " " endif |
         i in 1..3, j in 1..D
];









