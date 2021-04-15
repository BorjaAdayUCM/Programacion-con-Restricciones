include "all_different.mzn";

var int: r;

%Trabajos y funcionarios
int: n;

%tiempo de trabajo por funcionario
array[1..n,1..n] of int: t;

%1..n trabajador Y sol[i] = trabajo

%sol 
array[1..n] of var 1..n: sol; 

%un trabajo para cada uno
constraint all_different(sol);

constraint r = sum (i in 1..n) (t[i,sol[i]]);

solve minimize sum (i in 1..n) (t[i,sol[i]]);

output ["\(r)"];