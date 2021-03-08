%Número de niños.
int: n;
constraint assert (m > 0, "El número de niños debe ser mayor que cero");

%Satisfacción mínima.
int: s;
constraint assert (m > 0, "La satisfacción mínima debe ser mayor que cero");

%Número de juguetes.
int: m;
constraint assert (m > 0, "La cantidad de juguetes debe ser mayor que cero");

%Disponibilidad de cada juguete.
array[1..m] of int: disp;

%Tipos de juguete.
enum Tipo;

%Tipo de cada juguete.
array[1..m] of Tipo: jTipo;

%Satisfacción niño x juguete (puede ser negativa).
array[1..n, 1..m] of int: jSat;

%Asignaciones de niños y juguetes.
array[1..n, 1..2] of var 1..m: asig;

%No se asignan más juguetes de los disponibles.
constraint forall (i in 1..m) ((sum(j in 1..n, k in 1..2)(bool2int(asig[j,k] = i)) <= disp[i]));

%Todos mínima satisfacción.
constraint forall (i in 1..n) (sum(j in 1..2)(jSat[i,asig[i,j]]) >= s);

%No se entregan dos juguetes iguales.
constraint forall (i in 1..n) (jTipo[asig[i,1]] != jTipo[asig[i,2]]);

%Evitar redundancia de soluciones. Aparte de considerar AB igual que BA no te permite juguetes repetidos pues el primero debe ser menor que el siguiente.
constraint forall (i in 1..n) (asig[i,1] < asig[i,2]);

%solve satisfy;
solve maximize sum(i in 1..n, j in 1..2)(jSat[i, asig[i,j]]);

output ["N:  "] ++ ["\(i) " | i in 1..n] ++ ["\n"] ++
       ["J1: "] ++ ["\(asig[i,1]) " | i in 1..n] ++ ["\n"] ++
       ["J2: "] ++ ["\(asig[i,2]) " | i in 1..n];