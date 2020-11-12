--Javier Guzmán Muñoz
--Práctica Final Programación Declarativa
--Doble Grado en Ingeniería Informática-Matemáticas
---------------------------------------------------

-----------------
--PRIMERA PARTE--
-----------------

--Defincion de los tipos vñertice y grafo como se especificaba en el enunciado
data Vertice = A|B|C|D|E|F deriving (Eq ,Show, Read)
data Grafo = G [Vertice] [(Vertice, Vertice)] deriving (Show, Read)

{-Funcion que comprueba que un grafo dado lo es realmente, comprobando que los vertices no estan repetidos y que las aristas
unan vertices que esten en la lista de vertices del grafo -}
es_grafo::Grafo->Bool
es_grafo (G [] _) = False
es_grafo (G xs ys) = lista_sin_repetidos xs && aristas_en_lista xs ys

--Para comporbar lo anterior, necesitaremos tres funciones auxiliares
--La primera de ellas comprueba que dado un vertice, este pertence a la lista dada tambien
esta_en_lista::Vertice->[Vertice]->Bool
esta_en_lista v [] = False
esta_en_lista v (x:xs) = if v==x then True else esta_en_lista v xs

{- Esta funcion comprueba la primera condicion para que un supuesto grafo lo sea, que no contenga vertices repetidos.
Para ello, comprueba que cada vertice no esta en la lista de los que vienen a continuacion de el haciendo uso de la funcion anterior-}
lista_sin_repetidos::[Vertice]->Bool
lista_sin_repetidos [] = True
lista_sin_repetidos (x:xs) = not (esta_en_lista x xs) && (lista_sin_repetidos xs)

{-Esta funcion comprueba la segunda condicion para que sea grafo, que el origen y extremo de una arista sean vertices del grafo.
Para ello, comprueba que el extremo y el origen de cada arista esten en la lista de vertices del grafo haciendo uso de esta_en_lista-}
aristas_en_lista::[Vertice]->[(Vertice, Vertice)]->Bool
aristas_en_lista _ [] = True
aristas_en_lista xs ((x,y):ys) = (esta_en_lista x xs) && (esta_en_lista y xs) && (aristas_en_lista xs ys)

{-Construye la matriz de adyacencia de un grafo como lista de listas (donde cada lista representa una fila de la matriz).
Para hacer esto, para cada par de vertices, colocamos en la posicion correspondiente de la matriz la longitud de una lista con todas las aristas que 
van del primer vertice al segundo-}
mat_ady::Grafo->[[Int]]
mat_ady (G xs ys) = [[length[(z,w)|(z,w) <- ys, z == x, w == y]|y <-xs]| x <- xs]

{-Esta funcion unicamente devuelve una lista con la suma de los elementos de cada fila de la matriz de adyacencia-}
grados_pos::Grafo->[Int]
grados_pos = map sum.mat_ady

{-Los grados negativos es una lista con las sumas de los elementos de cada columna de la matriz.
Para ello, nos quedamos con el ultimo de coger n de cada fila (es decir, cogemos todos los elementos de la columna n) 
moviendo n entre 1 y el numero de vertices que tenemos y calculamos la suma de los valores de cada columna.-}
grados_neg::Grafo->[Int]
grados_neg (G xs ys) = [sum (map (last.(take n)) (mat_ady (G xs ys))) | n<-[1..(length xs)]]

{-Calcula recursivamente los caminos con origen en un vertice de una longitud dada.
Mediante una lista intensional recursiva, para todas las aristas con origen en v y final en w, añade el vertice v a los caminos 
de longitud n-1 emepzando en w. Además comprueba que el camino no contenga vertices repetidos, obviando así los posibles ciclos que puediera haber en el grafo.
Como caso base, se considera que un camino de longitud 0 desde un vertice es el propio vertice.
Esta función devuelve solo los caminos que no repiten ninguno de sus vertices, incluidos el primero y el ultimo, la funcion que devuelve lo que pide el enunciado,
los caminos de longitud n de acuerdo con la definicion estudiada en MDLM del primer curso, es ciclos_y_caminos_lng explicada e implementada más abajo. -}
caminos_lng::Int->Vertice->Grafo->[[Vertice]]
caminos_lng 0 v g = [[v]] 
caminos_lng n v (G xs ys) = [v:cam| (u,w)<-ys, u == v, cam <-(caminos_lng (n-1) w (G xs ys)), not (esta_en_lista v cam)]

{-Calcula todos los ciclos de longitud n desde un vertice dado. Para ello calcula todos los caminos sin repeticion de vertices (caminos_lng) de 
longitud n-1 y si hay una arista desde el ultimo vertice de ese camino hasta el primero la añade y consigue así un ciclo desde A de longitud n-}
ciclos_lng::Int->Vertice->Grafo->[[Vertice]]
ciclos_lng 0 v g = [[v]]
ciclos_lng n v (G xs ys) = [cam ++ [v] | (u,w) <- ys, cam <- (caminos_lng (n-1) w (G xs ys)), u == last cam, v == w]

{-Esta funcion es en verdad la que devuelve todos los caminos de longitud n desde un vertice si tenemos en cuenta la definición de camino dada en la asignatura
de matemática discreta en primero de carrera: un camino es un recorrido de vértices del grafo en el que todos los vertices son distintos entre sí excepto quizás
el primero y el último. Por tanto, concatenamos los dos conjuntos que podemos calcular con las funciones anteriores, el de los caminos de longitud n que no repiten 
ningun vértice, ni siquiera el primero ni el ultimo y los caminos que empiezan y acaban en el mismo vertice y no repiten ninguno de sus vertices intermedios.

EL RESULTADO DE ESTA FUNCION SERÍA EL QUE DEBERÍA DEVOLVER LA FUNCIÓN caminos_lng DEL ENUNCIADO DE LA PRÁCTICA, POR LO QUE SE CONSIDERA QUE ESTA ES LA RESPUESTA A
ESE APARTADO Y LAS DOS FUNCIONES ANTERIORES SON SOLO FUNCIONES AUXILIARES PARA IMPLEMENTAR ESTA Y SOBRE TODO LA FUNCIÓN conexo.-}
caminos_y_ciclos_lng::Int->Vertice->Grafo->[[Vertice]]
caminos_y_ciclos_lng 0 v g =[[v]]
caminos_y_ciclos_lng n v g = caminos_lng n v g ++ (ciclos_lng n v g)

{-Un grafo es conexo si para alguno de sus vertices existe un camino de cualquier longtud a todos los demás.
Como caso base se considera el grafo sin aristas, que obviamente no puede ser conexo.
En el caso general, elaboramos una lista intensional de booleanos en la que recogemos para cada vertice si existe un camino 
desde el hasta cada uno de los otros vertices o no. A la lista resutante la aplicamos un or (se define mediante un foldl) y así 
el resultado será True cuando haya algun vertice que lo cumpla y False en caso contrario. Para construir esta lista, construimos una
lista de listas, donde en cada posicion, correspondiente a un vertice del grafo, contiene la lista de todos los caminos que parten de el
de cualqueir longitud desde 0 hasta el numero de vertices, ya que al no considerar que los caminos pasen dos veces por el mismo vertice 
esta es la longitud maxima de la que podemos tener caminos (como mucho pasa por todos los vertices), y empezamos en 0 para obtener un camino
hacia el propio vertice que nos facilitara las cosas en la deficnicion de la funcion auxiliar llega_a_todos. Así, a cada elemento de esta lista
(que es a su vez una lista de caminos) le aplicamos la funcion que se define a continuacion y que nos dice si entre estos caminos hay al 
menos uno que acaba en cada unon de los vertices.-}
conexo::Grafo->Bool
conexo (G _ []) = False
conexo (G xs ys) = foldl (||) False (map (llega_a_todos xs) [concat[(caminos_lng n v (G xs ys)) | n <- [0..(length xs)]] | v<- xs ])

{-Funcion auxiliar para conexo que dada una lista de lista de vertices( que representan caminos en un grafo) determina si hay al menos un camino
en la lista que acabe en cada uno de los vertices de otra lista de vertices que le hemos pasado y que seran los vertices del grafo. Para ello,
comprueba que cada vertice de la lsiat de vertices del grafo xs este en una lista creada con los ultimos elementos de cada camino.-}
llega_a_todos::[Vertice]->[[Vertice]]->Bool
llega_a_todos xs xss = foldl (&&) True (map (flip esta_en_lista (map last xss)) xs)

--Isomorfismo de grafos

{-Las siguientes funciones auxiliares tienen por objetivo poder llegar a implementar una funcion que determine si dos grafos son isomorfos.
Para ello, usaremos que dos grafos osn isomorfos si existe alguna permutacion del orden de sus vertices tal que las matrices de adyacencia
asociadas son iguales.-}

{-Funcion que implementa el producto de dos matrices cuadradas de enteros de las mismas dimensiones. Como no se va a usar en para ese fin en
esta practica no se consideran matrices de dimensiones distintas que se puedan multiplicar o incluso matrices cuyo producto no sea posible.
Para implementar el producto, cada fila de la nueva matriz es el resultado de multiplicar esa fila en la primera matriz por cada columna de la
segunda, la funcion mat_por_cols respresenta una matriz por columnas.-}
prod_matrices::[[Int]]->[[Int]]->[[Int]]
prod_matrices [] _ = []
prod_matrices (m:m1) m2 = [map (prod_vect m) (mat_por_cols m2)] ++ (prod_matrices m1 m2)

--Funcion que define el producto escalar de dos vectores de enteros
prod_vect::[Int]->[Int]->Int
prod_vect v w= sum[x*y|(x,y)<-zip v w]

{-Funcion que dada una matriz de enteros como lista de listas de enteros (donde cada lista de enteros representa los elementos de una fila) devuelve
una matriz como lista de listas de enteros pero en la que cada lista de enteros representa los elementos de un a columna. Para ello, la primera columna
es el resultado de tomar el primer elemento (head) de cada fila e iteramos este proceso con el resto de cada fila (tail) y vamos concatenando los resultados.-}
mat_por_cols::[[Int]]->[[Int]]
mat_por_cols (x:xs) |x == [] = []  
                    |True = [map head (x:xs)]++mat_por_cols(map tail (x:xs))

{-Funcion que genera una lista de listas de listas de enteros, con n! elementos, donde cada lista de listas de enteros representa una matriz de permutacion
de un orden n dado. Para generar estas matrices, unicamente tenemos que permutar los elementos en [0..n-1] y colocar en cada fila de la matriz un 1 en la posicion
correspondiente al valor que haya en el vector [0..n-1] permutado en la posicion correspondiente a la fila que estamos construyendo. El resto lo rellenamos con 0's.
es decir, por ejemplo si n = 3, una posible permutacion del vector [0,1,2] es [1,0,2], lo que da lugar a la matriz [[0,1,0], [1,0,0], [0,0,1]]-}
genera_mat_perm::Int->[[[Int]]]
genera_mat_perm n = [[[if i == j then 1 else 0 | i<-[0..n-1]] | j <- permutacion] | permutacion <- perm [0..n-1]]

{-Funcion que dado un vector de eneteros genera todas las permutaciones sobre el mismo.
Funcion tomada directamente de la sesion 3 de laboratorio-}
perm::[Int]->[[Int]]
perm (x:[]) = [[x]]
perm xs = [x:ys| x <- xs, ys <- (perm ((takeWhile (/=x) xs) ++ tail(dropWhile (/=x) xs)))]

{-Comprueba si dos grafos son isomorfos. Para ellos, genera todas las posibles permutaciones de los vertices de una de ellas y las nuevas
matrices de adyacencia asociadas a estas permutaciones, y comprueba si alguna de ellas es igual a la matriz de adyacencia del otro grafo,
devolviendo True en caso afirmativo-}
isomorfos::Grafo->Grafo->Bool
isomorfos (G xs ys) (G zs ws)= or (map ((==) (mat_ady(G zs ws))) (mat_permutadas (mat_ady (G xs ys)) (genera_mat_perm (length xs))))

{-Dada una matriz y una lista con todas las matrices de permutacion de un orden dado, como las matrices de adyacencia representan los datos de los vertices
tanto en sus filas como en sus columnas, debemos hacer la misma permutacion tanto en filas como en columnas, es de ahí que las matrices permutadas (que representan
las matrices de adyacencia para un reordenamiento de los vertices) se obtengan multiplicando tanto por la izquierda como por la derecha cada matriz de permutacion 
a la amtriz concerta dada.-}
mat_permutadas::[[Int]]->[[[Int]]]->[[[Int]]]
mat_permutadas m perms = [prod_matrices (prod_matrices p m) p | p <- perms]

--Dos grafos son iguales si son isomorfos
instance Eq Grafo where
 (==) = isomorfos
 
 
-----------------
--SEGUNDA PARTE--
-----------------
 
{-Lee un grafo y devuleve un objeto del tipo IO Grafo.
Para ello primero pregunta el numero de vertices y pide que se introduzcan uno en cada linea.
Posteriormente pide el numero de aristas, pidiendo para cada una de llas el vertice de origen y de destino, cada uno en una linea.
Se presupone que los valores, para que puedan ser leidos, sean todos entre A y F.
Para los datos introducidos, comprueba que corresponden a un grafo correcto (funcion es_grafo) y en caso negativo itera el proceso hasta que introduzcamos 
un grafo valido-} 
leegrafo::IO Grafo
leegrafo = do print "Cuantos vertices tendra el grafo?: "
              numStr <-getLine
              n <-return (read numStr::Int)
              print ("Introduzca los " ++ (show n) ++ " vertices del grafo (uno por linea)")
              vertices <- leeVertices n
              print ("Cuantas aristas tendra el grafo?: ")
              numStr <- getLine
              n <- return (read numStr::Int)
              aristas <- leeAristas n
              if es_grafo (G vertices aristas) then do print "El grafo es correcto"
                                                       return (G vertices aristas)
                                               else do print "El grafo no es correcto"
                                                       leegrafo

--Necesitamos las siguientes funciones auxiliares:

--Lee n vertices introducidos por teclado, uno por linea.
leeVertices::Int->IO [Vertice]
leeVertices n =  if n == 0 then return []
                           else do vert <- getLine
                                   vertice <- return(read vert::Vertice)
                                   lista <- leeVertices (n-1)
                                   return (vertice:lista)

--Lee n aristas introducidas de una en una, con cada vertice en una linea.
leeAristas::Int->IO [(Vertice,Vertice)]
leeAristas n = if n == 0 then return []
                         else do print "Introduzca los dos vertices de una arista (uno por linea): "
                                 arista <- getLine
                                 v1 <- return(read arista::Vertice)
                                 arista <- getLine
                                 v2 <- return(read arista::Vertice)
                                 aristas <- leeAristas(n-1)
                                 return ((v1,v2):aristas)

--Lee un grafo e imprime su matriz de adyacencia
muestra_matriz::IO()
muestra_matriz = do grafo <- leegrafo
                    print "La matriz de adyacencia del grafo es: "
                    imprime_matriz (mat_ady grafo)

--Dada una matriz como lista de lista de enteros, imprime cada fila en una linea
imprime_matriz::[[Int]]->IO()
imprime_matriz [] = return ()
imprime_matriz (x:xs) = do print (show x)
                           imprime_matriz xs

{-Lee un grafo por teclado con lee_grafo y comprueba que sea conexo. En caso afirmativo, desde_donde contiene un vertice desde 
el que se puede llegar a todos los demas (y que hace que el grafo sea conexo). A continuacion se imprimen los caminos que nos 
proporciona la funcion caminos_a_mostrar, que contiene un camino que acaba en cada uno de los vertices del grafo y que empieza en desde_donde.-}
muestra_caminos::IO()
muestra_caminos = do (G xs ys) <- leegrafo
                     if conexo (G xs ys) then do desde_donde <- return (cualEsConexo xs (listaLlega (G xs ys)))
                                                 print ("El grafo es conexo, se puede llegar a todos los vertices desde " ++ (show desde_donde))
                                                 imprime_caminos (caminos_a_mostrar (G xs ys) desde_donde)
                                         else print "El grafo no es conexo"

--Dada una lista de caminos imprime cada uno de ellos en una linea
imprime_caminos::[[Vertice]]->IO()
imprime_caminos [] = return ()
imprime_caminos (c:cams) = do print (string_un_camino c)
                              imprime_caminos cams

--Dado un camino (lista de vertices) devuelve un String que representa el camino con sus elementos separados por guiones (-)
string_un_camino::[Vertice]->String
string_un_camino (x:[]) = show x
string_un_camino (x:xs) = (show x) ++ "-" ++ (string_un_camino xs)

--Lista de booleanos en la que el booleano en cada posicion indica si desde ese vertice existe al menos un camino para cada uno de losotros vertices.
--Esta lista es una parte de la definicion de la funcion conexo
listaLlega::Grafo->[Bool]
listaLlega (G xs ys) = map (llega_a_todos xs) [concat[(caminos_lng n v (G xs ys)) | n <- [0..(length xs)]] | v<- xs ]

--Dada una lista con los vertices de un grafo y una lista de booleanos (que sera la devuelta por la funcion anterior) determina que vertice es el primero
--desde el que se puede llegar a todos los demás.
cualEsConexo::[Vertice]->[Bool]->Vertice
cualEsConexo (x:xs) (l:lista) = if l then x else cualEsConexo xs lista

--Dado un grafo y un vertice de origen, selecciona para cada vertice de los restantes del grafo un camino que vaya desde el vertice origen hasta él.
--Para ello llama a la funcion uno cada con la lista de todos los caminos desde v de cualquier longitud entre 0 y el numero de vertices del grafo.
caminos_a_mostrar::Grafo->Vertice->[[Vertice]]
caminos_a_mostrar (G xs ys) v = uno_a_cada v xs (concat[(caminos_lng n v (G xs ys)) | n <- [0..(length xs)]])

--Dados un vertice v y una lista con todos los caminos desde ese vertice, para cada vertice que no sea v busca un camino
--que vaya desde v hasta ese otro vertice
uno_a_cada::Vertice->[Vertice]->[[Vertice]]->[[Vertice]]
uno_a_cada _ [] _ = []
uno_a_cada v (x:xs) ys = if v /= x then (busca_su_camino x ys):(uno_a_cada v xs ys) else uno_a_cada v xs ys

--Dado un vertice destino y una lista de caminos, busca el primer camino que tenga como extremo ese vertice y lo devuelve.
busca_su_camino::Vertice->[[Vertice]]->[Vertice]
busca_su_camino v (y:ys) = if v == last y then y else busca_su_camino v ys 

--Grafos para probar las funciones
--g1,g2,g3 son los dados en el enunciado de la practica
--g1 y g5 son isomorfos
--Todos son conexos (el menos evidente es  g6)
g1 = G [B,D,E,C] [(D,E),(E,B),(C,B),(E,C)]
g2 = G [D,F,E] [(D,F),(E,D),(D,E),(F,E)]
g3 = G [A,C,D] [(A,C),(C,D),(A,D)]
g4 = G [A,B,C,D,E,F] [(A,B),(A,C),(C,D),(D,E),(E,F),(B,A),(F,C),(F,F),(F,E)]
g5 = G [A,B,C,D] [(C,B),(B,D),(A,D),(B,A)]
g6 = G [A,B,C,D,E,F] [(B,A),(F,E),(D,E),(F,A),(A,C),(A,B),(F,F),(D,B),(B,D)]
