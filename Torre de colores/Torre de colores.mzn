% Use this editor as a MiniZinc scratch book
int: N = 5;
int: na = 3;
int: nr = 3;
int: nv = 1;


enum Colores = {azul, rojo, verde};

array[0..N-1] of var Colores: torre;

constraint forall (i in 0.. N - 2 where (torre[i] = verde)) (torre[i + 1] != verde);

%constraint sum (i in 0..N-1 where torre[i] = r)(1) > sum (i in 0..N-1 where torre[i] = v)(1) + sum (i in 0..N-1 where torre[i] = a)(1);

constraint sum(i in index_set(torre))(bool2int(torre[i] == rojo)) > (sum(i in index_set(torre))(bool2int(torre[i] == verde)) + sum(i in index_set(torre))(bool2int(torre[i] == azul)));
%constraint count(torre, r) > count(torre, v) + count(torre, a);

%constraint sum(i in 0..N-1)(bool2int(torre[i] == verde)) == 0;

constraint forall (i in 0.. N - 1) (sum(j in 0..i)(bool2int(torre[j] = verde)) <= sum(j in 0..i)(bool2int(torre[j] = azul)));


constraint torre[0] = rojo;

constraint sum(i in 0..N-1)(bool2int(torre[i] = azul)) <= na;
constraint sum(i in 0..N-1)(bool2int(torre[i] = rojo)) <= nr;
constraint sum(i in 0..N-1)(bool2int(torre[i] = verde)) <= nv;

solve satisfy;

output[ "\(torre[i])" ++ " " | i in 0..N-1];