% Use this editor as a MiniZinc scratch book
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


%Categorías de los trabajadores.
int: C;
array[1..T] of 1..C: Categorias;
array[1..3*C] of int: MinTC;

array[1..T, 1..D*3] of var bool: sol;


%Matriz de días libres.
array[1..T,1..D] of bool: DiasLibres;

%Matriz de turnos no deseados.
enum Turnos = {T1, T2, T3, L1};
array[1..T,1..D] of Turnos: TurnosNoDeseados;

%Asserts
constraint assert(D > 0, "Los días a organizar deben ser mayor que 0.");
constraint assert(T > N1 + N2 + N3, "No hay trabajadores suficientes para todos los turnos de un día.");
constraint assert(N1 > A /\ N2 > A /\ N3 > A, "Algún turno necesita más trabajadores para poder cumplir la restricción de afinidad.");
constraint forall(c in 1..C, t in 1..3)(assert(sum(j in 1..T)(Categorias[j] = c) > MinTC[C*(t-1) + c], "No hay suficientes trabajadores de la categoría \(c) para los turnos \(t)."));

%Cada turno tiene el número de trabajadores (N1, N2 o N3) que le corresponde.
constraint forall(i in 1..3*D where i mod 3 = 1)(sum(j in 1..T)(bool2int(sol[j, i])) = N1);
constraint forall(i in 1..3*D where i mod 3 = 2)(sum(j in 1..T)(bool2int(sol[j, i])) = N2);
constraint forall(i in 1..3*D where i mod 3 = 0)(sum(j in 1..T)(bool2int(sol[j, i])) = N3);

%Un trabajador solo puede trabajar un turno cada día.
constraint forall(i in 1..T, j in 1..3*D where j mod 3 = 1)(sol[i,j] -> (not sol[i, j + 1] /\ not sol[i, j + 2]));
constraint forall(i in 1..T, j in 1..3*D where j mod 3 = 2)(sol[i,j] -> (not sol[i, j - 1] /\ not sol[i, j + 1]));
constraint forall(i in 1..T, j in 1..3*D where j mod 3 = 0)(sol[i,j] -> (not sol[i, j - 2] /\ not sol[i, j - 1]));

%Un trabajador no trabaja MaxDT días seguidos.
constraint forall(i in 1..T, j in 1..3*D - 3*(MaxDT - 1) where j mod 3 = 1)(sum(k in j..j + (3*MaxDT - 1))(bool2int(sol[i,k])) < MaxDT);

%Un trabajador no libra MaxDL días seguidos.
constraint forall(i in 1..T, j in 1..3*D - 3*(MaxDL - 1) where j mod 3 = 1)(sum(k in j..j + (3*MaxDL - 1))(bool2int(sol[i,k] \/ DiasLibres[i, (j+2) div 3])) > 0);

%Un trabajador trabaja como mínimo MinDT días.
constraint forall(i in 1..T)(sum(j in 1..3*D where j mod 3 = 1)(bool2int(sol[i,j] \/ sol[i,j + 1] \/ sol[i,j + 2] \/ DiasLibres[i, (j+2) div 3])) >= MinDT);

%Un trabajador no puede hacer el último turno de un día y el primero del día siguiente dos veces consecutivas.
constraint forall(i in 1..T, j in 1..3*D - 3*3 where j mod 3 = 1)((sol[i,j + 2] /\ sol[i,j + 3] /\ sol[i,j + 8]) -> not sol[i,j + 9]);

%Cada trabajador trabaja con al menos A trabajadores afines en su turno.
constraint forall(i in 1..3*D, j in 1..T where sol[j, i])(sum(k in 1..T where j != k /\ sol[k, i])(Afinidad[j,k]) >= A);

%En cada turno hay mínimo un trbajador de cada categoría.
constraint forall(i in 1..3*D, c in 1..C where i mod 3 = 1)(sum(j in 1..T where Categorias[j] = c)(bool2int(sol[j,i])) >= MinTC[c]);
constraint forall(i in 1..3*D, c in 1..C where i mod 3 = 2)(sum(j in 1..T where Categorias[j] = c)(bool2int(sol[j,i])) >= MinTC[C * 1 + c]);
constraint forall(i in 1..3*D, c in 1..C where i mod 3 = 3)(sum(j in 1..T where Categorias[j] = c)(bool2int(sol[j,i])) >= MinTC[C * 2 + c]);





/***************PROBLEMA DE SATISFACCIÓN***************/

%Los trabajadores libran los días que han pedido.
constraint forall(i in 1..T, j in 1..D)(DiasLibres[i,j] -> (sol[i,(j*3)-2] = false /\ sol[i,(j*3)-1] = false /\ sol[i,(j*3)] = false));

%Los trabajadores no trabajan los turnos que han pedido no trabajar.
constraint forall(i in 1..T, j in 1..D)((TurnosNoDeseados[i,j] = T1) -> (sol[i, (j * 3) - 2] = false));
constraint forall(i in 1..T, j in 1..D)((TurnosNoDeseados[i,j] = T2) -> (sol[i, (j * 3) - 1] = false));
constraint forall(i in 1..T, j in 1..D)((TurnosNoDeseados[i,j] = T3) -> (sol[i, (j * 3)] = false));

solve satisfy;

/******************************************************/







/***************PROBLEMA DE OPTIMIZACIÓN***************/

%Minimiza el número de días libres pedidos no concedidos.
%solve minimize sum(i in 1..3*D, j in 1..T where i mod 3 = 1)(bool2int(DiasLibres[j, (i + 2) div 3] /\ (sol[j, i] \/ sol[j, i + 1] \/ sol[j, i + 2])));

%Minimiza el número de turnos no deseados pedidos no concedidos.
%solve minimize sum(i in 1..3*D, j in 1..T where i mod 3 = 1)(bool2int((TurnosNoDeseados[j, (i + 2) div 3] = T1 /\ sol[j, i]) \/ (TurnosNoDeseados[j,(i + 2) div 3] = T2 /\ sol[j, i + 1]) \/ (TurnosNoDeseados[j,(i + 2) div 3] = T3 /\ sol[j, i + 2])));

%Minimiza el número de días libres pedidos y turnos no deseados no concedidos.
%solve minimize sum(i in 1..D, j in 1..T)(bool2int(TurnosNoDeseados[j,i] != L1 /\ sol[j,i] = TurnosNoDeseados[j,i]) + bool2int(DiasLibres[j,i] /\ not (sol[j,i] = L1)));

/******************************************************/



output [ if (fix(sol[i,j])) then "T1" elseif (fix(sol[i,j + 1])) then "T2" elseif (fix(sol[i,j + 2])) then "T3" else "L1" endif ++  
         if j == 3*D-2 then "\n" else " " endif |
         i in 1..T, j in 1..D*3 where j mod 3 = 1
];


