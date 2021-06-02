% Use this editor as a MiniZinc scratch book

int: NAceitesVegetales;
int: NAceitesNoVegetales;
int: NAceites = NAceitesVegetales + NAceitesNoVegetales;

int: meses;

int: K;

int :T;

array[1..meses, 1..NAceites] of int: precios;
%Precio de venta mensual
array[1..meses] of int: preciosMensual;

int: MAXV;
int: MAXN;

int: MCAP;
%Maxima capacidad del almacén de aceite refinado.
int: MCAPR;

int: CA;
int: CAR;

float: MinD;
float: MaxD;

array[1..NAceites] of float: durezas;

array[1..NAceites] of int: restanteFinal;

array [1..NAceites, 1..NAceites] of bool: aceitesAUsar;

int: MinB;

array[1..meses, 1..NAceites] of var 0..MCAP: compras;
array[1..meses, 1..NAceites] of var 0..max(MAXV, MAXN): refinado;
array[1..meses] of var 0..(MAXN + MAXV + MCAPR): ventaMensual;

var int: beneficio;

function var int: restanteMes(array[1..meses, 1..NAceites] of var int: compras, array[1..meses, 1..NAceites] of var int: refinado, int: mes, int: aceite) = if mes = 0 then 0 
                                                                                                                                       else sum(i in 1..mes)(compras[i, aceite] - refinado[i, aceite]) endif;
                                                                                                                                     
                                                                                                                                                    
function int: restanteMes(array[1..meses, 1..NAceites] of int: compras, array[1..meses, 1..NAceites] of int: refinado, int: mes, int: aceite) = if mes = 0 then 0
                                                                                                                                        else sum(i in 1..mes)(compras[i, aceite] - refinado[i, aceite])
                                                                                                                                        endif;

function var int: restanteMesRefinado(array[1..meses, 1..NAceites] of var int: refinado, array[1..meses] of var int: ventaMensual, int: mes) = if mes = 0 then 0 
                                                                  else sum(i in 1..mes, j in 1..NAceites)(refinado[i, j]) - sum(i in 1..mes)(ventaMensual[i]) endif;
                                                                                                                                        
%Como maximo refinamos la cantidad disponible de cada aceite.
constraint forall(i in 1..meses, j in 1..NAceites)(refinado[i, j] <= (compras[i, j] + restanteMes(compras, refinado, i - 1, j)));

%Como máximo se refinan MAXV toneladas de acites vegetales mensualmente y MAXN toneladas de aceites no vegetales.
constraint forall(i in 1..meses)(sum(j in 1..NAceitesVegetales)(refinado[i, j]) <= MAXV /\ sum(j in NAceitesVegetales + 1..NAceites)(refinado[i, j]) <= MAXN);

%Como máximo se almacenan MCAP tonaladas de cada aceite.
constraint forall(i in 1..meses, j in 1..NAceites)((compras[i, j] + restanteMes(compras, refinado, i - 1, j)) <= MCAP);

%Al final de los meses deben quedar en los almacenes la cantidad exacta de cada aceite.
constraint forall(i in 1..NAceites)(restanteMes(compras, refinado, meses, i) = restanteFinal[i]);

%La dureza final de nuestro producto está entre MinD y MaxD.
constraint forall(i in 1..meses)(sum(j in 1..NAceites)(refinado[i, j] * durezas[j]) <= MaxD * sum(j in 1..NAceites)(refinado[i, j]) /\ sum(j in 1..NAceites)(refinado[i, j] * durezas[j]) >= MinD * sum(j in 1..NAceites)(refinado[i, j]));

%Beneficio. (Suponemos el almacenaje de julio no cuesta dinero)
constraint beneficio = sum(i in 1..meses)(ventaMensual[i] * preciosMensual[i]) - sum(i in 1..meses, j in 1..NAceites)(compras[i, j] * precios[i, j]) - sum(i in 1..meses, j in 1..NAceites)(compras[i, j] + restanteMes(compras, refinado, i - 1, j)) * CA - sum(i in 1..meses)(restanteMesRefinado(refinado, ventaMensual, i - 1)) * CAR;

%No usamos más de K aceites mensualmente.
constraint forall(i in 1..meses)(sum(j in 1..NAceites)(bool2int(refinado[i, j] > 0)) <= K);

%Si un aceite es usado, debe usarse más de T toneladas.
constraint forall(i in 1..meses, j in 1..NAceites)(refinado[i, j] > 0 -> refinado[i, j] >= T);

%Cumplimos las restricciones de uso de aceites.
constraint forall(i in 1..meses, j in 1..NAceites, k in 1..NAceites)(refinado[i, j] > 0 /\ aceitesAUsar[j, k] = 1 -> refinado[i, k] > 0);

%No puedo vender a final de mes más de lo que tengo refinado.
constraint forall(i in 1..meses)(ventaMensual[i] <= sum(j in 1..NAceites)(refinado[i, j]) + restanteMesRefinado(refinado, ventaMensual, i - 1));

%El almacén de aceite refinado no puede superar MCAPR toneladas.
constraint forall(i in 1..meses)(restanteMesRefinado(refinado, ventaMensual, i) <= MCAPR);

constraint beneficio >= MinB;

%solve satisfy;
solve maximize beneficio;

output ["\(beneficio)"] ++ ["\n\n"] ++ 
       [ "\(compras[i,j])" ++ if j == NAceites then "\n" else " " endif | i in 1..meses, j in 1..NAceites] ++ ["\n\n"] ++ 
       [ "\(refinado[i,j])" ++ if j == NAceites then "\n" else " " endif | i in 1..meses, j in 1..NAceites] ++ ["\n\n"] ++ 
       [ "\(ventaMensual[i])\n" | i in 1..meses] ++ ["\n\n"] ++ 
       [ "\(restanteMes(compras, refinado, i,j))" ++ if j == NAceites then "\n" else " " endif | i in 1..meses, j in 1..NAceites];