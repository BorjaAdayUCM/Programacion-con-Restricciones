%Número de objetos.
int: n;
constraint assert (n > 0, "El número de objetos debe ser mayor que cero");

%Número de papeleras.
int: k;
constraint assert (k > 0, "El número de papeleras debe ser mayor que cero");

%Volumen de las papeleras.
int: V;

%Volumen de cada objeto.
array[1..n] of int: volume;
constraint assert (forall (i in 1..n)(volume[i] <= V), "El volumen de cada objeto no puede superar V");

%Solución.
array[1..n] of var 1..k: sol;

%En cada papelera no hay objetos cuya suma de volumen sea mayor que V.
constraint forall (i in 1..k) (sum(j in 1..n where sol[j] = i)(volume[j]) <= V);

%solve satisfy;

solve maximize sum(i in 1..k where count(sol, i) = 0)(1);

output ["\(sol[i]) " | i in 1..n];