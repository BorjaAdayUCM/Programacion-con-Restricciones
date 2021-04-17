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
array[1..T,1..D] of var Turnos: sol;

%Categorías de los trabajadores.
int: C;
array[1..T] of 1..C: Categorias;
array[1..3*C] of int: MinTC;

%Matriz de días libres.
array[1..T,1..D] of bool: diasLibres;

%Matriz de turnos no deseados.
array[1..T,1..D] of Turnos: turnosNoDeseados;

%Asserts
constraint assert(D > 0, "Los días a organizar deben ser mayor que 0.");
constraint assert(T > N1 + N2 + N3, "No hay trabajadores suficientes para todos los turnos de un día.");
constraint assert(N1 > A /\ N2 > A /\ N3 > A, "Algún turno necesita más trabajadores para poder cumplir la restricción de afinidad.");
constraint forall(c in 1..C, t in 1..3)(assert(sum(j in 1..T)(Categorias[j] = c) > MinTC[C*(t-1) + c], "No hay suficientes trabajadores de la categoría \(c) para los turnos \(t)."));



%Cada turno tiene el número de trabajadores (N1, N2 o N3) que le corresponde.
constraint forall(i in 1..D)(sum(j in 1..T)(bool2int(sol[j,i] = T1)) = N1);
constraint forall(i in 1..D)(sum(j in 1..T)(bool2int(sol[j,i] = T2)) = N2);
constraint forall(i in 1..D)(sum(j in 1..T)(bool2int(sol[j,i] = T3)) = N3);

%Un trabajador solo puede trabajar un turno cada día.
%Esta restricción se cumple siempre por la forma en la que representamos el problema.

%Un trabajador no trabaja MaxDT días seguidos.
constraint forall(i in 1..T, j in 1..D - (MaxDT - 1))(sum(k in j..j + (MaxDT - 1))(bool2int(sol[i,k] != L1)) < MaxDT);

%Un trabajador no libra MaxDL días seguidos. (Los días libres que se pide cuentan como trabajados).
constraint forall(i in 1..T, j in 1..D - (MaxDL - 1))(sum(k in j..j + (MaxDL - 1))(bool2int(sol[i,k] = L1 /\ not diasLibres[i,k])) < MaxDL);

%Un trabajador trabaja como mínimo MinDT días. (Los días libres que se pide cuentan como trabajados).
constraint forall(i in 1..T)(sum(j in 1..D)(bool2int(sol[i,j] != L1 \/ diasLibres[i,j])) >= MinDT);

%Un trabajador no puede hacer el último turno de un día y el primero del día siguiente dos veces consecutivas.
constraint forall(i in 1..T, j in 1..D - 3)((sol[i,j] = T3 /\ sol[i,j + 1] = T1 /\ sol[i,j + 2] = T3) -> sol[i,j + 3] != T1);

%Cada trabajador trabaja con al menos A trabajadores afines en su turno.
constraint forall(i in 1..D, j in 1..T where sol[j, i] != L1)(sum(k in 1..T where j != k /\ sol[j, i] = sol[k, i])(Afinidad[j,k]) >= A);

%En cada turno hay mínimo un trbajador de cada categoría.
constraint forall(i in 1..D, c in 1..C)(sum(j in 1..T)(bool2int(sol[j, i] = T1 /\ Categorias[j] = c)) >= MinTC[c]);
constraint forall(i in 1..D, c in 1..C)(sum(j in 1..T)(bool2int(sol[j, i] = T2 /\ Categorias[j] = c)) >= MinTC[C*1 + c]);
constraint forall(i in 1..D, c in 1..C)(sum(j in 1..T)(bool2int(sol[j, i] = T3 /\ Categorias[j] = c)) >= MinTC[C*2 + c]);




/***************PROBLEMA DE SATISFACCIÓN***************/

%Los trabajadores no trabajan los turnos que han pedido no trabajar.
constraint forall(i in 1..T, j in 1..D)((turnosNoDeseados[i,j] != L1) -> sol[i,j] != turnosNoDeseados[i,j]);

%Los trabajadores libran los días que han pedido.
constraint forall(i in 1..T, j in 1..D)(diasLibres[i,j] -> sol[i,j] = L1);

solve satisfy;

/******************************************************/







/***************PROBLEMA DE OPTIMIZACIÓN***************/

%Minimiza el número de días libres pedidos no concedidos.
%solve minimize sum(i in 1..D, j in 1..T)(bool2int(diasLibres[j,i] /\ not (sol[j,i] = L1)));

%Minimiza el número de turnos no deseados pedidos no concedidos.
%solve minimize sum(i in 1..D, j in 1..T)(bool2int(turnosNoDeseados[j,i] != L1 /\ sol[j,i] = turnosNoDeseados[j,i]));

%Minimiza el número de días libres pedidos y turnos no deseados no concedidos.
%solve minimize sum(i in 1..D, j in 1..T)(bool2int(turnosNoDeseados[j,i] != L1 /\ sol[j,i] = turnosNoDeseados[j,i]) + bool2int(diasLibres[j,i] /\ not (sol[j,i] = L1)));

/******************************************************/







/******************SOLUCIÓN****************************/
output [ "\(sol[i,j])" ++ 
         if j == D then "\n" else " " endif |
         i in 1..T, j in 1..D
];









