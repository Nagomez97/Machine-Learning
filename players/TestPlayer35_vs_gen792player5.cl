(defpackage :mancala
  (:use :common-lisp)
  (:export :*debug-level*
	   :*debug-nmx*
	   :*tournament*
	   :*verb*
	   :*verjugada*
	   :*vermarcador*
	   :acciones-posibles
	   :cuenta-fichas
	   :ejecuta-accion
	   :estado
	   :estado-debe-pasar-turno
	   :estado-lado-sgte-jugador
	   :estado-lado-sgte-jugador
	   :estado-tablero
	   :estado-tablero
	   :f-j-humano
	   :generar-sucesores
	   :get-fichas
	   :get-pts
	   :get-tot
	   :juego-terminado-p
	   :juego-terminado-p
	   :jugador
	   :jugador-nombre
	   :lado-contrario
	   :lado-contrario
	   :list-lado
	   :make-jugador
	   :negamax
	   :partida
	   :pide-accion
	   :posiciones-con-fichas-lado
	   :put-tablero-aux
	   :reset-tablero-aux
	   :suma-fila
	   ))
(in-package mancala)

;; SBL
(declaim #+sbcl(sb-ext:muffle-conditions style-warning))
(defmacro my-with-timeout ((seconds &body timeout-body) &body body)
  `(handler-case
      (sb-ext:with-timeout ,seconds ,@body)
      (sb-ext:timeout (e) ,@timeout-body)))

;; Allegro
;(defmacro my-with-timeout  ((seconds &body timeout-body) &body body)
;   `(sys:with-timeout (,seconds ,@timeout-body) ,@body))

;;; ==========================================================================================
;;; PRACTICAS IA. PRACTICA 4 (JUEGOS)
;;;
;;; MANCALA - v.10.0 P2P 2017
;;; Implementa una version del juego Mancala con las variantes expuestas en la P4 de 2017
;;;
;;; NUEVO EN LA VERSION 10.
;;; - Acumulador revisado para que solo cuente fichas capturadas, ignorando las obtenidas de otros modos.
;;; - Se incluye mecanismo de fuga de fichas de Kalaha propio a hoyos contrarios.
;;;
;;; NUEVO EN LA VERSION 9.
;;; - Adaptado para Modern Lisp
;;;
;;; NUEVO EN LA VERSION 8.
;;; - 8.2: Al alcancar el maximo de jugadas: si alguien tiene 19+ gana, en caso contrario tablas.
;;; - 8.1: El acumulador cuenta solo fichas capturadas, no las ganadas por mala gestion contraria
;;; - Se rehabilita el Kalaha y el mecanismo de juego del Mancala original
;;; - Converge mas rapido por lo que se reduce a 50 el numero maximo de jugadas.
;;;
;;; NUEVO EN LA VERSION 7.
;;; - No hay modificaciones funcionales sobre la version 6.31, sin embargo, los
;;;   parametros del juego han sido elegidos para reducir la longitud de las
;;;   partidas, ello permite reducir a 100 el numero maximo de jugadas.
;;;
;;; NUEVO EN LA VERSION 6.31
;;; - el modo *verb* muestra tambien las jugadas de los jugadores automaticos
;;; - el bucle de lectura de jugadas permite modificar parametros con setq|setf, lo cual
;;;   permite modificar el nivel de verbosidad durante una partida
;;; - los nombres de jugadores que empezaban por *jugador... pasan a *jdr...
;;; - incorpora funciones P2P (requiere Allegro +8.2 y cargar mancala6_p2p_b.fasl)
;;;
;;; NUEVO EN LA VERSION 6.30
;;; - Incluye funciones de manejo de un tablero auxiliar
;;; - Evita que quien devuelva un nº negativo muy grande (que puede pasar por nil) obtenga
;;;   tablas. Del mismo modo, si el humano abandona no obtiene tablas sino que pierde.
;;;
;;; COMENTARIOS
;;; NOTA: Las normas del juego son las publicadas. Esta minidoc es solo a efectos de mantenimiento.
;;; - Jugar con profundidad 2 es mas que suficiente para evaluar jugadores y mucho mas rapido que 3 o 4
;;; - Resumen de la variante *m6* :
;;;   * Se permite mover en ambos sentidos, al modo de las damas holandesas.
;;;   * Si se termina de sembrar en un hoyo:
;;;      a) Vacio, termina la jugada actual.
;;;      b) Con menos de X fichas y el contrario tiene menos de Y en el hoyo y menos de Z
;;;         en total, se ceden al contrario nuestras fichas y termina la jugada actual.
;;;      c) Si no es aplicable (b) y hay fichas en el hoyo propio y en el contrario: se
;;;         roban al contrario sus fichas y se sigue sembrando.
;;;      d) En cualquier otro caso se termina la jugada actual.
;;;
;;; EJECUCION
;;; - Cargar el fichero
;;; - Ejecutar alguna de las partidas de prueba que hay al final del fichero
;;; - Puede iniciarse el juego en cualquier posicion, utilizando la variable opcional filas
;;; - Cargar version compilada para mayor eficiencia
;;;            (COMPILE-FILE "D:/ARCHI/uni/Doce/14/ia/p3/mancala8.cl")
;;;            (load "D:/ARCHI/uni/Doce/14/ia/p3/mancala8.fasl")
;;;
;;; NOTAS
;;;   (*) Alguna de las mejoras introducidas no se ha aplicado al Mancala original por lo que
;;;   de momento no estan operativas mas que las versiones Mancala2 y Mancala6
;;;
;;; ==========================================================================================

;;; ------------------------------------------------------------------------------------------
;;; VARIABLES GLOBALES
;;;                   Mancala2  Mancala6  Mancala7  Mancala/8
;;; *long-fila*          8         8         8         6
;;; *fichas-inicio*      3         3         3         3
;;; *fichas-jugador*    15        15        15        18
;;; *kalaha*            nil       nil       nil        t
;;; *inicio-siembra*     1         1         1         1
;;; *m6*                nil        t        nil       nil
;;; *2-sentidos*        nil        t        nil       nil
;;; ------------------------------------------------------------------------------------------

(defvar *vers*           "11.0") ; Version "x.y" = mancala X, rel. Y
(defvar *long-fila*        6   ) ; longitud de la fila de cada jugador, incl. el Kalaha en su caso
(defvar *fichas-inicio*    3   ) ; numero de fichas que hay inicialmente en cada hueco
(defvar *fichas-jugador*   18  ) ; numero total de fichas por jugador
(defvar *kalaha*           t   ) ; t=con hoyo almacen (Kalaha), nil=sin Kalaha
(defvar *inicio-siembra*   1   ) ; posicion desde la que se empieza a sembrar
(defvar *m6*               nil ) ; t=Mancala5
(defparameter *2-sentidos*       nil ) ; Switch doble sentido: t=movimiento en ambos sentidos, nil=sentido unico
(defparameter *verb*             nil   ) ; Switch verbose: imprime comentarios sobre evolucion del programa
(defparameter *verjugada*        nil   ) ; Switch para ver cada jugada (nil = reduce print, p.e. en juego automatico
                                 ; y en su lugar saca una barra para seguir la evolucion de la actividad)
(defparameter *vermarcador*      nil   ) ; Switch para ver el marcador si *verjugada*=nil
(defvar *maxjugadas*       60  ) ; num maximo de jugadas antes de dar la partida por tablas
(defvar *tablas*           nil ) ; indicador de tablas
(defvar *k*   (if *kalaha* 1 0)) ; variable auxiliar para contar o no con Kalaha
(defvar *max-tengo*        4   ) ; maximo numero de fichas en ultimo hoyo para poder capturar
(defparameter *tournament*       nil ) ; t=juego llamado desde torneo, nil=juego individual
(defparameter *marcador*  (make-array '(2 2) :initial-element 0))
(defparameter *prof*             0   ) ; Profundidad al expandir nodo
(defparameter *tablero-aux*      nil ) ; Tablero auxiliar para uso discrecional del alumno (solo mediante funciones especificas)
(defconstant +max-val+   99999 ) ; Valor maximo para negamax y otros usos
(defconstant +min-val+  -99999 ) ; Valor minimo para negamax y otros usos

(setf (symbol-function 'r) #'1+) ; Definicion del operador R (siembra a derechas)
(setf (symbol-function 'l) #'1-) ; Definicion del operador L (siembra a izquierdas)

;;; creacion de las cabeceras superior e inferior del tablero
(defvar +hdr1+ (format nil "~{ ~2D~}" (let ((result nil)) (dotimes (i *long-fila* result) (push i result)))))
(defvar +hdr0+ (format nil "~{ ~2D~}" (reverse (let ((result nil)) (dotimes (i *long-fila* result) (push i result))))))
;;; formatos para la impresion de lineas y espacios del tablero
(defvar +fmt1+ (concatenate 'string "~%  ~" (format nil "~A" (* *long-fila* 3)) "{-~}"))
(defvar +fmt2+ (concatenate 'string "~"     (format nil "~A" (* *long-fila* 3)) "{ ~}"))

(defvar *hist-1*)             (defvar *hist-2*)                (defvar *avge1*)              (defvar *avge2*)
(defvar *njugada*)            ;(defparameter *jdr-humano*)            (defparameter *jdr-human2*)         (defparameter *jdr-aleatorio*)
;(defparameter *jdr-1st-opt*)        (defparameter *jdr-last-opt*)          (defparameter *jdr-nmx-bueno*)      (defparameter *jdr-nmx-regular*)
;(defparameter *jdr-erroneo*)        (defparameter *jdr-nmx-eval-aleatoria*)
(defparameter *logfile* t)          (defvar *timeout* 20)
(defparameter *thumano* 900)        (defparameter *debug-level* 2)         (defparameter *debug-nmx* nil)

;;; Solo para versiones superiores a ACL 6.2
;;; Esto deberia funcionar, pero falla en ACL 6.2
;;; (if (packagep (find-package 'cg.base)) (import 'cg.base:copy-array))
;;; Pero ha hecho falta hacerlo asi para la ACL 6.2:
;(format t "~2%Game v.~A " *vers*)
;(cond ((find-package 'cg.base) (format t "cg.base already loaded or Lisp Ver. > 8~%"))
;      (t (import 'copy-array (make-package 'cg.base))
;         (export (find-symbol "COPY-ARRAY" 'cg.base) 'cg.base)))

(defun copy-array (array)
 (let ((dims (array-dimensions array)))
   (adjust-array
    (make-array dims :displaced-to array)
    dims)))

;;; ------------------------------------------------------------------------------------------
;;; ESTRUCTURA PARA REPRESENTAR UN ESTADO DEL JUEGO
;;; ------------------------------------------------------------------------------------------

(defstruct estado
  tablero                        ; como esta el tablero en el momento
  lado-sgte-jugador              ; lado del tablero a cuyo jugador corresponde mover
  debe-pasar-turno               ; flag: t= EL siguiente jugador debe pasar turno, porque el otro
                                 ; realizo una accion que le permite volver a mover (Mancala1)
  accion)                        ; accion que ha llevado a la posicion actual

;;; ------------------------------------------------------------------------------------------
;;; ESTRUCTURA PARA REPRESENTAR UN JUGADOR (incl. P2P)
;;; ------------------------------------------------------------------------------------------

(defstruct jugador
  nombre                         ; nombre mostrado por pantalla para el jugador
  f-juego                        ; funcion de busqueda del jugador
  f-eval                         ; funcion de evaluacion del jugador: negamax u otra
  (host  "" :type string)        ; ""= no p2p, "a.b.c.d"=p2p local o remoto
  (port 0 :type integer))        ; puerto de comunicaciones (0=no p2p)

;;; ------------------------------------------------------------------------------------------
;;; FUNCIONES DE ACCESO AL TABLERO (ENCAPSULAN AREF EN LAS FUNCIONES DE BUSQUEDA)
;;; ------------------------------------------------------------------------------------------

;;; Pone cuantas fichas en determinada posicion del lado del tablero de un jugador
(defun put-fichas (tablero lado posicion cuantas)
  (setf (aref tablero lado posicion) cuantas))

;;; Obtiene el numero de fichas en determinada posicion del lado del tablero de un jugador
(defun get-fichas (tablero lado posicion)
  (aref tablero lado posicion))

;;; Anade una ficha en determinada posicion del lado del tablero de un jugador
(defun anade-ficha (tablero lado posicion)
  (setf (aref tablero lado posicion) (+ 1 (aref tablero lado posicion))))

;;; Anade cuantas fichas en determinada posicion del lado del tablero de un jugador
(defun anade-fichas (tablero lado posicion cuantas)
  (setf (aref tablero lado posicion) (+ cuantas (aref tablero lado posicion))))

;;; Cuenta las fichas que hay en la zona del tablero de un jugador desde la posicion desde hasta el final
(defun cuenta-fichas (tablero lado desde)
  (suma-fila tablero lado *long-fila* desde))

;;; Suma por filas los n elementos decimales de una matriz m de fils filas y cols columnas
;;; Devuelve una lista con fils valores. La lista esta en orden inverso.
;;; Uso: (suma-array (estado-tablero estado) 2 8) => (suma-fila1 suma-fila0)
(defun suma-array (m fils cols)
  (let ((sumas nil))
    (dotimes (i fils sumas)
      (push (suma-fila m i cols) sumas))))

;;; Suma los elementos desde a hasta de la fila fi de una matriz m [fils x cols]
;;; Rango de indices de una matriz de n cols = 0 a n-1. Eg: elementos 3+4+5 de la fila 0:
;;; (suma-fila (estado-tablero estado) 0 6 2)
(defun suma-fila (m fi &optional (hasta (+ *k* *long-fila*)) (desde 0) )
  (let ((suma 0))
    (do ((j desde (1+ j))) ((= (+ j desde) hasta)) (incf suma (aref m fi (+ j desde))))
    suma))

;;; Elimina las fichas que hay en la zona del tablero de un jugador
(defun limpia-fichas (tablero lado desde)
  (cond
   ((>= desde *long-fila*) nil)
   (t
    (put-fichas tablero lado desde 0)
    (limpia-fichas tablero lado (+ 1 desde)))))

;;; Funciones discrecionales del alumno para modificar un array auxiliar semejante al tablero

(defun reset-tablero-aux (&optional (x 0))
  "si *tablero-aux* existe lo reinicializa (si no, lo crea) inicializando a x"
  (if *tablero-aux*
      (dotimes (i (+ *long-fila* *long-fila*) *tablero-aux*) (setf (row-major-aref *tablero-aux* i) x))
    (setq *tablero-aux* (make-array (list 2 (+ *k* *long-fila*)) :initial-element x))))

(defun put-tablero-aux (lado posicion cuantas)
  (setf (aref *tablero-aux* lado posicion) cuantas))

;;; ------------------------------------------------------------------------------------------
;;; FUNCIONES DE INICIALIZACION DE TABLERO Y ESTADO
;;; ------------------------------------------------------------------------------------------

;;; Crea la lista para el initial-contents de la parte de tablero de un jugador
(defun construye-fila-tablero (long fichas)
  (cond
   ((= 0 long) (if *kalaha* '(0) nil))
   ( t (if (>= fichas *fichas-inicio*)
           (cons *fichas-inicio* (construye-fila-tablero (- long 1) (- fichas *fichas-inicio*)))
           (cons fichas (construye-fila-tablero (- long 1) fichas))))))

;;; Crea las listas para el initial-contents del tablero
(defun construye-tablero ()
  (let ((fila (construye-fila-tablero *long-fila* *fichas-jugador*)))
    (if (not *kalaha*) (setq fila (reverse fila)))
    (list fila fila)))

;;; Crea un estado inicial
(defun crea-estado-inicial (lado-sgte-jugador &optional filas)
  (make-estado
   :tablero (make-array (list 2 (+ *k* *long-fila*))
              :initial-contents (if (null filas) (construye-tablero) filas ))
   :lado-sgte-jugador lado-sgte-jugador
   :accion            nil))

;;; ------------------------------------------------------------------------------------------
;;; OTRAS FUNCIONES PARA TRABAJAR CON EL TABLERO
;;; ------------------------------------------------------------------------------------------
;;; Muestra el tablero
;;;   Jugador 1 : lado superior del tablero (i.e. invertido)
;;;   Jugador 0 : lado inferior del tablero

(defun muestra-tablero (estado &optional fin)
  (let ((jug-act (if fin 99 (estado-lado-sgte-jugador estado)))
        (tablero (estado-tablero estado)))
    (format t " ~%TABLERO: ")
    (format t "~2% ~A" +hdr1+)
    (format t +fmt1+ '(""))
    (print-lado (list-lado estado 1) jug-act 1)                  ; fila superior
    (when *kalaha*                                               ; fila central
      (format t "~%~2D" (aref tablero 1 *long-fila*))
      (format t +fmt2+ '(""))
      (format t "~2A" (aref tablero 0 *long-fila*)))
    (print-lado (reverse (list-lado estado 0)) jug-act 0)        ; fila inferior
    (format t +fmt1+ '(""))
    (format t "~% ~A" +hdr0+)))

;;; Imprime un lado del tablero y marca la posicion activa
(defun print-lado (lado jug-act posi)
  (format t "~%~A" (if (= jug-act posi) "*" " "))
  (format t "~{ ~2D~}" lado)
  (format t "     ~2D  Ac: ~2D" (get-pts posi) (get-tot posi)))

;;; Devuelve una lista con el estado de un lado del tablero en orden inverso
(defun list-lado (estado n)
  (let ((result nil))
    (dotimes (i *long-fila* result)
      (push (aref (estado-tablero estado) n i) result))))

;;; Devuelve la lista de posiciones, para un jugador, que tienen alguna ficha
(defun posiciones-con-fichas-lado (tablero lado desde)
  (cond
   ((>= desde *long-fila*) nil)
   ((< 0 (aref tablero lado desde))
    (cons desde (posiciones-con-fichas-lado tablero lado (+ 1 desde))))
   (t
    (posiciones-con-fichas-lado tablero lado (+ 1 desde)))))

(defun combina-elt-lst (elt lst)
  "Devuelve las combinaciones del elemento atomico elt con una lista"
  (mapcar #'(lambda (x) (list elt x)) lst))

(defun combina-lst-lst (lst1 lst2)
  "Devuelve el producto cartesiano de dos listas"
  (unless (null lst1)
    (append
     (combina-elt-lst (first lst1) lst2)
     (combina-lst-lst (rest lst1) lst2))))

;;; ------------------------------------------------------------------------------------------
;;; FUNCIONES DE ACCESO AL MARCADOR (ENCAPSULAN AREF)
;;; ------------------------------------------------------------------------------------------

(defun reset-contadores (n)
  (reset-marcador)
  (setq *hist-1* (make-list n :initial-element *fichas-jugador*)
        *hist-2* (make-list n :initial-element *fichas-jugador*)
        *avge1* (* n *fichas-jugador*)
        *avge2* *avge1*
        *njugada* 0
        *tablas* nil ))

;;; Actualiza marcadores. Devuelve nil salvo si se pide marcador.
(defun act-marcador (tablero lado &key marcador)
  (let ((pts0 (suma-fila tablero 0))
        (pts1 (suma-fila tablero 1))
        (old-pts0 (get-pts 0))
        (old-pts1 (get-pts 1)))
    (when lado
      (set-pts 0 pts0)
      (set-pts 1 pts1)
      (when (and (> old-pts0 0) (> old-pts1 0))                  ; Acumula en total si no es inicio partida
        (set-tot lado (+ (get-tot lado)
                         (max (if (= lado 0) (- pts0 old-pts0) (- pts1 old-pts1)) 0)))))
    (when marcador (list pts0 pts1))))

;;; Funciones de acceso al marcador
(defun get-pts (i) (aref *marcador* 0 i))
(defun get-tot (i) (aref *marcador* 1 i))
(defun set-pts (i pts) (setf (aref *marcador* 0 i) pts))
(defun set-tot (i pts) (setf (aref *marcador* 1 i) pts))

(defun reset-marcador () (dotimes (i 4) (setf (row-major-aref *marcador* i) 0)))

;;; ------------------------------------------------------------------------------------------
;;; FUNCIONES FUNDAMENTALES DE LA PARTIDA
;;; ------------------------------------------------------------------------------------------

;;; Devuelve el jugador oponente
(defun lado-contrario (lado)
  (if (= lado 0) 1 0))

;;; Cambia el sgte-jugador de un estado, teniendo tambien en cuenta si debe pasar turno
;;; Devuelve el estado tras el cambio
(defun cambia-lado-sgte-jugador (estado debe-pasar-turno)
  (setf (estado-lado-sgte-jugador estado) (lado-contrario (estado-lado-sgte-jugador estado)))
  (setf (estado-debe-pasar-turno  estado) debe-pasar-turno)
  estado)

;;; Devuelve las acciones posibles para un jugador dado el estado
(defun acciones-posibles (estado)
  (if (estado-debe-pasar-turno estado)
      (list nil)
    (let ((l-acciones (posiciones-con-fichas-lado (estado-tablero estado)
                                                  (estado-lado-sgte-jugador estado) 0))
          (sentidos (if *2-sentidos* '(r l) '(r))))
          (combina-lst-lst sentidos l-acciones))))

;;; Hace una copia del estado
;;; TBD: revisar necesidad. copy-estado no crea copia del array.
(defun copia-estado (estado &optional accion)
  (make-estado
   :tablero                (copy-array  (estado-tablero estado))
   :lado-sgte-jugador      (estado-lado-sgte-jugador estado)
   :accion                 (if accion accion (estado-accion estado))))

;;; Ejecuta una accion del juego
;;; Si la accion es nil pasa turno (cambia de lado)
;;; Devuelve un estado tras el cambio de lado

(defun ejecuta-accion (estado accion)
  (when *verb* (format t "~%Juega ~A " accion))
  (if  accion
      (let* ((fmov (first accion))
             (hoyo (second accion))
             (nuevo-estado (copia-estado estado accion))
             (tablero (estado-tablero nuevo-estado))
             (lado (estado-lado-sgte-jugador nuevo-estado))
             (numero-fichas (get-fichas tablero lado hoyo))
             (fichas (suma-fila tablero lado (1+ *long-fila*))))
        (put-fichas tablero (estado-lado-sgte-jugador estado) hoyo 0)
        ;(format t "~%  tablero pre  distribuye :~a" tablero)
        (let ((sigue? (distribuye-fichas tablero lado numero-fichas (mov fmov hoyo) t fmov)))
          (cambia-lado-sgte-jugador nuevo-estado sigue?)))
    (cambia-lado-sgte-jugador (copia-estado estado accion) nil)))

(defun mov (fmov n)
  "aplica f. de movimiento a posicion n"
  (let ((newn (funcall fmov n)))
    (mod (if (< newn 0) (+ *k* *long-fila* newn) newn) (+ *k* *long-fila*))))

;;; Realiza recursivamente la siembra de fichas en una jugada
;;;
;;; tablero     : estruct del tablero a actualizar
;;; lado        : lado del tablero que juega
;;; cuantas     : numero de fichas a sembrar
;;; desde       : hoyo inicial de siembra
;;; es-su-zona  : t|nil segun el jugador este o no en su propia zona
;;; fmov        : funcion de movimiento para la siembra (def=1+)
;;;
;;; Devuelve t  : sigue jugando (porque deja la ultima ficha en el kalaha)
;;;          nil: no sigue y pasa turno al contrario

(defun distribuye-fichas (tablero lado cuantas desde &optional es-su-zona fmov)
  (cond
   ((and (>= desde *long-fila*) (> cuantas 1))                          ; caso en el que damos la vuelta
    (cond
     (*kalaha*                                                          ; si modalidad Kalaha
      (anade-ficha tablero lado *long-fila*)                            ; pasa sobre Kahala dejando una ficha
      (distribuye-fichas tablero (lado-contrario lado) (1- cuantas) 0 (not es-su-zona) fmov))
     (t (distribuye-fichas tablero lado cuantas 0 es-su-zona fmov))))
   ((<= cuantas 1)                                                      ; colocando la ultima ficha
    (let* ((tengo (get-fichas tablero lado desde))
           (hoyo-contrario (- *long-fila* desde 1))                     ; =-1 = caso Kalaha
           (captura (if (>= hoyo-contrario 0)                           ; Si fichas en contrario y no Kalaha (> -1)
                        (get-fichas tablero (lado-contrario lado) hoyo-contrario)
                      0)))                                              ; Ult. ficha en Kalaha => sin captura
      (when *verb* (format t " => Ultima ficha en ~D, con ~D, contra: ~D" desde tengo captura))
      (cond
       ((and *kalaha* (= desde *long-fila*))                            ; fin en Kalaha ...
        (anade-ficha tablero lado desde)
        (cond ((and es-su-zona (> (get-fichas tablero lado desde) 1))   ; Si es el propio y no vacio, juega de nuevo
               (show (format nil " => Kalaha y sigue jugando"))
               t)
              (t (show (format nil " => Kalaha contrario o vacio. Cede turno"))  ; Si estaba vacio o es K contrario, termina
                 nil)))
       ;; caso en que ultima ficha cae en propia casilla vacia (Mancala) o llena (Mancala2+)
       ((and es-su-zona (funcall (if *kalaha* #'= #'>) tengo 0))
        (cond
         (*kalaha*                                                      ; Mancala/8/9 (cada version con codigo distinto)
          (cond
           ((> captura 0)                                               ; Si hay captura roba y termina
            (show (format nil " => Captura ~D y termina" captura))
            (anade-fichas tablero lado *long-fila* (+ 1 captura))
            (put-fichas tablero (lado-contrario lado) hoyo-contrario 0)
            nil)
           (t (anade-fichas tablero lado desde cuantas)                 ; Si no hay captura termina
              nil)))
         (t                                                             ; Mancala2+
          (let ((total-contr (suma-fila tablero (lado-contrario lado))))
            (cond                                                       ; Hay entrega o captura?
             ((and *m6* (> tengo 4)(< captura 3)(< total-contr *long-fila*)(> total-contr 0)) ; Entrega
              (put-fichas tablero lado desde 0)
              (put-fichas tablero (lado-contrario lado) hoyo-contrario (+ captura 1 tengo))
              (show (format nil " (Total ~D). Entrega" total-contr) tablero)
              nil)
             ((and (> tengo 0) (< tengo *max-tengo*) (> captura 0))     ; Captura
              (anade-ficha tablero lado desde)
              (put-fichas tablero (lado-contrario lado) hoyo-contrario 0)
              (show (format nil "~% Captura ~D y siembra-~A" captura fmov))
              (distribuye-fichas tablero lado captura (mov fmov desde) es-su-zona fmov))
             (t (anade-ficha tablero lado desde)
                (show (format nil ". Ni captura ni entrega") tablero)
                nil))))))
       ((and (not es-su-zona) *kalaha* (> tengo 5) (= captura 0))       ; Robo especifico Mancala9: termina en contrario>5 y propias=0
        ;;(format t "~%Robo especifico M10: sembrando en contrario tengo=0 (~A) y contrario>5 (~A)" captura tengo)
        (put-fichas tablero lado desde 0)                               ; Roba a contrario y termina
        (put-fichas tablero (lado-contrario lado) hoyo-contrario (+ tengo 1))
        (show (format nil " => Roba (Entrega Inversa) ~D+1 del contrario y cede turno." tengo))
        nil)
       (t                                                               ; cualq.otro caso en q pone ultima ficha
        (anade-ficha tablero lado desde)
        (show "" tablero)
        nil))))
   (t                                                                   ; cualq.otro caso en q pone 1 ficha (no ultima)
    (anade-ficha tablero lado desde)
    (distribuye-fichas tablero lado (1- cuantas) (mov fmov desde) es-su-zona fmov)) ))

(defun show (txt &optional tablero)
  "muestra situacion para seguimiento juego"
  (when *verb*
    (format t "~A~A" txt (if tablero
                             (format nil ": ~a" (act-marcador tablero nil :marcador t))
                           ","))))

;;; Genera los posibles sucesores de un estado
;;; SIDEFECT: A efectos de trazabilidad (No necesario para el juego), guarda la profundidad.
(defun generar-sucesores (estado &optional profundidad)
  (when *verb* (format t "~% -------- Gen.Sucesores de ~a    [Prof:~a]" (estado-tablero estado)
                 (if profundidad (progn (setq *prof* 0) profundidad)
                                       (format nil "0.~3,'0d" (incf *prof*)))))
  (unless (juego-terminado-p estado)
    (mapcar #'(lambda(x) (ejecuta-accion estado x)) (acciones-posibles estado))))

;;; Pide una accion al usuario entre las posibles
(defun pide-accion (posibles-acc)
  (format t "~%Jugador Humano. ~%  Elija entre: ~A~%  o en modo abreviado: ~A~%  Introduzca jugada o x para terminar : "
    posibles-acc (abreviado posibles-acc))
  (let ((input (read)))
    (unless (eq 'x input)
      (let ((accion (if (numberp input)
                        (list (if (>= (signum input) 0) 'r 'l) (abs input))
                      input)))
        (cond
         ((and (listp accion)
               (or (eq (car accion) 'setq) (eq (car accion) 'setf))
               (member (second accion) '(*verb* *verjugada* *vermarcador*)))
          (eval accion) (format t "~%OK")
          (pide-accion posibles-acc))
         ((member accion posibles-acc :test #'equal) accion)
         (t (format t "~%Sintaxis: (S P)|PA  Donde S=sentido siembra, P=posicion valida, PA=posicion en modo abreviado ~%~10TModo abreviado: n>=0 = (R |n|), n<0 = (L |n|)" )
            (pide-accion posibles-acc)))))))

;;; Presenta en modo abreviado las posibles acciones
(defun abreviado (posibles-acc)
  (mapcar #'(lambda (x) (ccase (car x)
                          ('r (second x))
                          ('l (if (= (second x) 0) x (- (second x))))))
    posibles-acc))

;;; Funcion predicado que comprueba si el estado es de fin de partida
(defun juego-terminado-p (estado)
  (let ((tablero (estado-tablero estado)))
    (or
     (<= (suma-fila tablero 0 *long-fila*) (- 1 *k*))
     (<= (suma-fila tablero 1 *long-fila*) (- 1 *k*)))))

;;; Dadas dos puntuaciones devuelve t si una de las dos obtiene una media
;;; de 2 puntos en las ultimas N jugadas o si sobrepasan el *maxjugadas*
;;;
;;; Notese que para evitar realizar divisiones en cada ciclo lo que se hace es comparar
;;; no las medias con 2 sino la suma con un numero igual a (* 2 *long-fila*), que tambien
;;; coincide con el numero de jugadas en la que se comprueba la media.
;;; En el caso de Kahala se resta, pues lo que importa son los hoyos normales.

(defun tablas-p (tablero)
  (let* ((n (* 2 *long-fila*))
         (i (mod *njugada* n))
         (pts1-k (if *kalaha* (- (get-pts 0) (aref tablero 0 *long-fila*)) (get-pts 0)))
         (pts2-k (if *kalaha* (- (get-pts 1) (aref tablero 1 *long-fila*)) (get-pts 1))))
    (setf *avge1* (+ *avge1* (- (nth i *hist-1*)) pts1-k)
      *avge2* (+ *avge2* (- (nth i *hist-2*)) pts2-k)
      (nth i *hist-1*) pts1-k
      (nth i *hist-2*) pts2-k)
    ;;(format t "~% [J ~3D] 0: ~A = ~A~%         1: ~A = ~A " *njugada* *hist-2* *avge2* *hist-1* *avge1*)
    (cond
     ((or (>= *njugada* *maxjugadas*) (<= *avge1* n) (<= *avge2* n) )
      (setq *tablas* t))
     (t (incf *njugada*)
        (setq *tablas* nil)))))

;;; Informa al usuario que ha terminado el juego, mostrando el marcador
(defun informa-final-de-juego (estado lst-jug &optional msg winner)
  (let* ((pts0 (get-pts 0))
         (pts1 (get-pts 1))
         (tablero (estado-tablero estado))
        (ganador (cond
                  (*tablas*
                   (if *kalaha*
                       (cond       ;; Si Kalaha y tablas, comprueba si alguno tiene mas de la mitad en su Kalaha
                        ((> (aref tablero 0 *long-fila*) *fichas-jugador*) 1)
                        ((> (aref tablero 1 *long-fila*) *fichas-jugador*) 2)
                        (t 0))
                     0))
                  (msg winner)
                  ((< pts0 pts1) 2)
                  ((> pts0 pts1) 1)
                  (t 0 ))))
    (when (and (> *debug-level* 1) (not *tournament*))
      (format t "~2%  FIN DEL JUEGO por ~A en ~A Jugadas~%  Marcador:  ~A ~A - ~A ~A~%~%"
        (if (= ganador 0) "TABLAS" "VICTORIA")
        *njugada*
        (jugador-nombre (first lst-jug))
        pts0
        pts1
        (jugador-nombre (second lst-jug))))
    (values ganador nil)))

;;; ------------------------------------------------------------------------------------------
;;; FUNCION PRINCIPAL PARA REALIZAR UNA PARTIDA ENTRE DOS JUGADORES
;;; ------------------------------------------------------------------------------------------
;;; RECIBE:
;;;  - lado:  Lado del tablero a cuyo jugador le corresponde comenzar a jugar
;;;           0=2=Jugador1 (abajo);  1=Jugador2 (arriba)
;;;  - profundidad-max: maxima profundidad de la busqueda negamax
;;;  - lst-jug-partida: (Jugador1 Jugador2)
;;;    Lista compuesta por los dos structs jugador que tomaran parte en la partida.
;;;  - filas: Parametro opcional que fuerza situacion inicial tablero
;;; DEVUELVE: resultado de la partida (0=tablas, 1=gana Jugador1, 2=gana Jugador2)
;;; ------------------------------------------------------------------------------------------

(defun partida (lado profundidad-max lst-jug &optional filas)
  (let* ((lado-01 (mod lado 2))
         (estado (crea-estado-inicial lado-01 filas))
         (boast (/= (jugador-port (second lst-jug)) 0))
         (chall (/= (jugador-port (first lst-jug)) 0)) )
    (reset-contadores (* 2 *long-fila*))
    (if (or *tournament* (and (< *debug-level* 2) (not boast) (not chall)))
        (setq *verjugada* nil *vermarcador* nil)
      (if *verjugada* (format t "~%  Juego: (1) ~a vs ~a (2) "
                        (jugador-nombre (first lst-jug)) (jugador-nombre (second lst-jug)))))
    (local-loop estado lado-01 profundidad-max lst-jug)))

;;; =======================================================================================
;;: LOOP LOCAL
;;; =======================================================================================

(defun local-loop (estado lado-01 profundidad-max lst-jug)
  "bucle de movimientos alternos hasta conclusion de la partida"
  (when *verb* (format t "~%Local game ~A-~A depth=~A " (jugador-nombre (first lst-jug)) (jugador-nombre (second lst-jug)) profundidad-max))
  (loop
    (let ((ult-lado (mod (+ 1 lado-01) 2)))
      (act-marcador (estado-tablero estado) ult-lado)
      (when (and *verb* (estado-accion estado))
        (format t "~%[J ~A] ~A juega ~A "
          *njugada* (jugador-nombre (nth ult-lado lst-jug)) (estado-accion estado))))
    (let ((curr-plyr (nth lado-01 lst-jug)))
        (cond
         ((or (juego-terminado-p estado)                                ; si juego terminado o tablas
              (tablas-p (estado-tablero estado)))
          (when *verjugada* (muestra-tablero estado t))
          (return (informa-final-de-juego estado lst-jug)))
         (t                                                             ; llamada al jugador que tiene el turno
          (cond
           ((estado-debe-pasar-turno estado)
            (when *verb* (format t "~%[J ~A] ~A pasa turno." *njugada* (jugador-nombre curr-plyr)))
            (cambia-lado-sgte-jugador  estado  nil)
            (setf (estado-accion estado) nil))
           (t
            (if *verjugada*
                (progn
                  (muestra-tablero estado)
                  (format t "~%[J ~A] El turno es de ~A~%" *njugada* (jugador-nombre curr-plyr)))
              (if *vermarcador*
                  (format t "~%~3d ~a-~a" *njugada* (get-pts 0) (get-pts 1))
                (when (= (mod *njugada* 10) 0)
                  (to-logfile (format nil " ~d" *njugada*) 4 t))))
            (setf estado
              (my-with-timeout ((get-timeout curr-plyr) (to-logfile " T-Out " 2 t) 'timeout)
	;	(ignore-errors
		  (funcall (jugador-f-juego curr-plyr)
			   estado
			   profundidad-max
			   (jugador-f-eval curr-plyr))
         ;)
    ))))
	  (when (null estado)                                           ; => abandono, error o return nil|-infinito
            (return (values (winner (nth lado-01 lst-jug) lst-jug) "Error en func. o abandono")))
          (when (eql estado 'timeout)                                   ; timeout de jugada
            (return (values (winner (nth lado-01 lst-jug) lst-jug) "Timeout jugada")))
          (setf lado-01 (mod (1+ lado-01) 2)))))))                      ; inversion: pasa al otro jugador / convierte 1-2 0-1

(defun get-timeout (plyr)
  (cond
   ((eq (jugador-f-juego plyr) #'f-j-humano) *thumano*)
   (t *timeout*)))

(defun winner (loser lst-jug)
  "Devuelve quien es el ganador de la partida"
  (if (eq (jugador-nombre loser) (jugador-nombre (first lst-jug))) 2 1))

;;; ------------------------------------------------------------------------------------------
;;; FUNCIONES DE BUSQUEDA
;;; ------------------------------------------------------------------------------------------

;;; ------------------------------------------------------------------------------------------
;;; ALGORITMO NEGAMAX
;;; ------------------------------------------------------------------------------------------
;;; Funcion que inicia la busqueda y devuelve el siguiente estado elegido por el jugador que
;;; tiene el turno, segun algoritmo negamax
;;; RECIBE:   estado,
;;;           profundidad-max    : limite de profundidad
;;;           f-eval             : funcion de evaluacion
;;; DEVUELVE: estado siguiente del juego
;;; ------------------------------------------------------------------------------------------

(defun negamax (estado profundidad-max f-eval)
  (let* ((oldverb *verb*)
         (*verb* (if *debug-nmx* *verb* nil))
         (estado2 (negamax-1 estado 0 t profundidad-max f-eval))
         (*verb* oldverb))
    estado2))

;;; ------------------------------------------------------------------------------------------
;;; Funcion auxiliar negamax-1
;;; RECIBE:   estado, profundidad-actual,
;;;           devolver-movimiento: flag que indica si devolver un estado (llamada raiz) o un valor numerico (resto de llamadas)
;;;           profundidad-max    : limite de profundidad
;;;           f-eval             : funcion de evaluacion
;;; DEVUELVE: valor negamax en todos los niveles de profundidad, excepto en el nivel 0 que devuelve el estado del juego tras el
;;;           movimiento que escoge realizar
;;; ------------------------------------------------------------------------------------------
(defun negamax-1 (estado profundidad devolver-movimiento profundidad-max f-eval)
  (cond ((>= profundidad profundidad-max)
         (unless devolver-movimiento  (funcall f-eval estado)))
        (t
         (let ((sucesores (generar-sucesores estado profundidad))
               (mejor-valor +min-val+)
                (mejor-sucesor nil))
           (cond ((null sucesores)
                  (unless devolver-movimiento  (funcall f-eval estado)))
                 (t
                  (loop for sucesor in sucesores do
                    (let* ((result-sucesor (- (negamax-1 sucesor (1+ profundidad)
                                        nil profundidad-max f-eval))))
                      ;(format t "~% Nmx-1 Prof:~A result-suc ~3A de suc ~A, mejor=~A" profundidad result-sucesor (estado-tablero sucesor) mejor-valor)
                      (when (> result-sucesor mejor-valor)
                        (setq mejor-valor result-sucesor)
                        (setq mejor-sucesor  sucesor))))
                  (if  devolver-movimiento mejor-sucesor mejor-valor)))))))

;;; ------------------------------------------------------------------------------------------
;;; Implementacion del algoritmo negamax con poda alfa-beta
;;; ------------------------------------------------------------------------------------------

;;; (defun negamax-a-b (estado profundidad-max f-eval)
;;;   ...)

;;; ------------------------------------------------------------------------------------------
;;; FUNCIONES AUXILIARES
;;; ------------------------------------------------------------------------------------------

;;; Si el log es a fichero y este no esta abierto, informa del error y lo intenta en consola
;;; con una llamada recursiva. Evita bucle infinito poniendo a t from-error.
(defun to-logfile (msg lvl &optional contline from-error)
  (when (<= lvl *debug-level*)
    (if (ignore-errors
         (if contline
             (format *logfile* "~A" msg)
           (multiple-value-bind (ss mn hh dd mm yy) (get-decoded-time)
             (if (= lvl 0)
                 (format *logfile* "~%~2,'0D~2,'0D~2,'0D ~2,'0D~2,'0D~2,'0D ~A"
                   hh mn ss (- yy 2000) mm dd msg)
               (format *logfile* "~%~2,'0D~2,'0D~2,'0D ~A" hh mn ss msg))))
         (force-output *logfile*)
         t)
        msg
      (unless from-error
        (format t "~%ERROR escritura en ~a. ~%Reintento a consola." *logfile*)
        (setq *logfile* t)
        (to-logfile msg lvl contline t)))))

;;; Aborta la ejecucion                                                         [AdS 2008]
;;; ------------------------------------------------------------------------------------------
(defun @stop (&optional (msg "Abortado por usuario"))
 (handler-bind ((error #'invoke-debugger))
                      (error msg)))

;;; f-juego controlado por un humano
;;; ------------------------------------------------------------------------------------------
(defun f-j-humano (estado &optional profundidad-max f-eval)
  (and profundidad-max f-eval)      ; dummy to avoid compiler warnings
  (setq *verjugada* t)
  (let ((accion (pide-accion (acciones-posibles estado))))
    (unless (null accion) (ejecuta-accion estado accion))))








;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Jugadores predefinidos
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; f-juego que utiliza busqueda negamax (con o sin poda)
;;; ------------------------------------------------------------------------------------------
(defun f-j-nmx (estado profundidad-max f-eval)
;;;(negamax-a-b estado profundidad-max f-eval))
  (negamax estado profundidad-max f-eval))

;;; Jugador Bueno (debido a que juega con un nivel mas de evaluacion)
;;; ------------------------------------------------------------------------------------------
(defun f-eval-Bueno (estado)
  (if (juego-terminado-p estado)
      -50                              ;; Condicion especial de juego terminado
    ;; Devuelve el maximo del numero de fichas del lado enemigo menos el numero de propias
    (max-list (mapcar #'(lambda(x)
                          (- (suma-fila (estado-tablero x) (lado-contrario (estado-lado-sgte-jugador x)))
                             (suma-fila (estado-tablero x) (estado-lado-sgte-jugador x))))
                (generar-sucesores estado)))))

(defvar *jdr-nmx-Bueno* (make-jugador
                        :nombre   '|Ju-Nmx-Bueno|
                        :f-juego  #'f-j-nmx
                        :f-eval   #'f-eval-Bueno))

;;; Devuelve el top segun test de una lista de nos. y su posicion
(defun max-list (l &key (test #'max))
  (let ((m (reduce test l)))
    (values m (position m l))))

;;; Jugador Regular
;;; ------------------------------------------------------------------------------------------
(defun f-eval-Regular (estado)
  (- (suma-fila (estado-tablero estado) (estado-lado-sgte-jugador estado))
     (suma-fila (estado-tablero estado) (lado-contrario (estado-lado-sgte-jugador estado)))))

(defvar *jdr-nmx-Regular* (make-jugador
                        :nombre   '|Ju-Nmx-Regular|
                        :f-juego  #'f-j-nmx
                        :f-eval   #'f-eval-Regular))

;;; Jugador Mio
;;; ------------------------------------------------------------------------------------------
; Posibles fichas a kalaha
(defun mis-kalahas (num lado)
  (if (null lado)
      0
    (+ (mis-kalahas (+ num 1)(rest lado))
       (if (equal (+ num
                     (first lado)) 
                  6)
           -5
         0))))

; Fichas en el kalaha
(defun cuenta-kalaha (tablero lado)
  (get-fichas tablero lado 6))

; Posiciones de posible captura
(defun capturas (tablero pos mi-lado otro-lado)
  (if (equal pos 6)
      0
    (- (capturas tablero (+ 1 pos) mi-lado otro-lado)
       (if (equal 0 
                  (get-fichas tablero mi-lado pos))
           (get-fichas tablero otro-lado (- 5 pos))
         1))))

; Cuencas vacias en el jugador
(defun vacios (tablero pos lado)
  (if (equal pos 6)
      0
    (+ (vacios tablero (+ 1 pos) lado)
       (if (equal (get-fichas tablero lado pos) 1)
           1
         0))))


(defun mi-f-eval (estado)
  (+ (cuenta-kalaha (estado-tablero estado) 
                    (estado-lado-sgte-jugador estado))
     (get-pts (estado-lado-sgte-jugador estado))
     (vacios (estado-tablero estado)
             0
             (estado-lado-sgte-jugador estado))))


(defun mi-acumulador (estado)
  (get-tot (estado-lado-sgte-jugador estado)))

(defun mi-f-eval (estado)
  (+ (cuenta-kalaha (estado-tablero estado) 
                    (estado-lado-sgte-jugador estado))
     (get-pts (estado-lado-sgte-jugador estado))
     (vacios (estado-tablero estado)
             0
             (estado-lado-sgte-jugador estado))
     (mi-acumulador estado)))

(defvar *test4* (make-jugador
                        :nombre   '|test3|
                        :f-juego  #'f-j-nmx
                           :f-eval   #'mi-f-eval))




;(defun mi-f-ev (estado)
;  (+ (mis-kalahas 0 (list-lado estado (estado-lado-sgte-jugador estado))) 
;     (capturas (estado-tablero estado) 
;               0 
;               (estado-lado-sgte-jugador estado) 
;               (lado-contrario (estado-lado-sgte-jugador estado)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; JUGADORES ENTREGADOS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun F-GAZOR-1 (estado)
  (+ (mis-kalahas 0 (list-lado estado (estado-lado-sgte-jugador estado)))
     (cuenta-kalaha (estado-tablero estado) 
                    (estado-lado-sgte-jugador estado))
     (* 2 (get-pts (estado-lado-sgte-jugador estado)))))

(defvar *gazor1* (make-jugador
                        :nombre   '|gazor-1|
                        :f-juego  #'f-j-nmx
                           :f-eval   #'F-GAZOR-1))


(defun F-GAZOR-2 (estado)
  (+ (mis-kalahas 0 (list-lado estado (estado-lado-sgte-jugador estado))) 
     (get-pts (estado-lado-sgte-jugador estado))))

(defvar *gazor2* (make-jugador
                        :nombre   '|gazor-2|
                        :f-juego  #'f-j-nmx
                  :f-eval   #'F-GAZOR-2))

(defun F-GAZOR-3 (estado)
  (+ (cuenta-kalaha (estado-tablero estado) 
                    (estado-lado-sgte-jugador estado))
     (get-pts (estado-lado-sgte-jugador estado))
     (vacios (estado-tablero estado)
             0
             (estado-lado-sgte-jugador estado))))

(defvar *gazor3* (make-jugador
                        :nombre   '|gazor-3|
                        :f-juego  #'f-j-nmx
                  :f-eval   #'F-GAZOR-3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Jugador mutable
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun prod-escalar (v1 v2)
  (apply #'+ (mapcar #'* v1 v2)))

(defun matriz-x-vector (m v)
  (mapcar #'(lambda (fila) (prod-escalar fila v)) m))

(defun suma-vectores (v1 v2)
  (mapcar #'+ v1 v2))

(defun inputs (estado)
  (let ((tablero (estado-tablero estado))
        (mi-lado (estado-lado-sgte-jugador estado)))
      (append (input-lado tablero mi-lado 0)
            (input-lado tablero (lado-contrario mi-lado) 0))))

(defun input-lado (tablero lado pos)
  (unless (equal pos 7)
    (cons (get-fichas tablero lado pos)
          (input-lado tablero lado (+ 1 pos)))))


(defun h_TestPlayer35 (estado)
(+ -0.14059802013995681
(prod-escalar '(0.7825081444408835 -0.6122781876109427 0.9773728634749999 -0.9167309196518205 -0.7061569469494975 0.859880678508429 -0.020726608069931984 -0.7623794036126099 -0.6515103403039386 0.18132533448386767)
(suma-vectores '(-0.3451921608588182 -0.0008914268950876991 -0.12793409105777354 0.7761652032898219 0.9854244527309932 0.9009567371993781 -0.2776745200030102 -0.11701097733811694 0.7915224103177312 -0.8072886049664874)
(matriz-x-vector '((0.3033141208612944 -0.7952410488822808 -0.683885207074209 0.7259234281316203 0.05962086017710044 0.7635706100689217 0.4434268491733131 -0.1580473147336532 0.4275429442431298 0.456706321178749 -0.3959731295425857 0.27705713999975057 -0.2796893506907816 -0.9295882967045259)
 (0.353110981671271 0.7373608493519184 0.49179566990482537 -0.20684090134866406 -0.5066153035336425 0.8287723748669413 0.7492977997023551 -0.06716020272898193 0.32057563711189974 -0.8001014962635142 0.3964800233146133 -0.1508503042737479 0.4955564457673365 -0.26346403394333606)
 (0.7443459938902162 0.2625103697453157 0.7302653871393217 0.12186698904631021 -0.6176563022586024 -0.45672033655048594 0.5415081232216359 0.13362172375378423 -0.7152232777446639 0.6204257845739873 -0.7043787011550457 -0.14537057132742404 0.0297847728770817 0.11418716544346297)
 (-0.8466596845181706 -0.10669560403765543 -0.5434983773524471 0.16132601992183493 -0.4033959752229761 -0.6707391940594323 0.2118629343388987 -0.09390974337357183 0.8233795771418473 0.15193042185995598 0.12228164979804923 0.492547492118834 0.15866225521652622 0.17144355174098025)
 (0.8174521711312521 0.907667630714998 -0.36638246886517 0.41265771847726773 0.9617437414652863 0.6321913660256351 -0.5010695384020358 0.4974319003446779 0.262086860435347 0.3152943574265925 0.20460034038766017 -0.8849311932979571 -0.5515129135166921 -0.4746139210147078)
 (0.7181165089081114 0.33514373353981886 0.26516717148339786 0.7688708243371212 -0.8467062083678316 -0.36491054046882865 -0.814873203445909 -0.6616276174641471 -0.7629617682420395 -0.5929221212449329 0.4542628921066809 -0.7505551890691968 0.6785237044359522 -0.009102380688849276)
 (0.5149912969344255 -0.9917371074217491 0.16221230645106877 0.7878007123422146 -0.05849964440976407 0.6559951324485129 -0.17061204504977368 0.3471837778223774 0.10649065411755254 0.20666804260323146 0.9306144779919217 0.49244761877531773 -0.5678061080592587 -0.06486095911242296)
 (0.4084166292552116 0.7394534465298725 -0.99550542583726 -0.0841959593719892 -0.6572892651883218 0.2692570022109555 0.5892772177595629 0.03546828338394148 0.34301028139344236 0.8007647118535475 -0.43558320937885764 0.8130379897452926 0.5069573783245798 -0.7545531828603234)
 (0.2075996165552414 0.021355411737075558 -0.22640728803272525 0.7549473861405218 -0.4455361455063309 0.24344557877439543 0.7550085974534286 -0.25988114783657723 -0.40259197344684194 0.8850888780844304 0.9850841575354208 -0.63918351612899 0.685742355137648 0.3802610581733723)
 (0.536544429887899 -0.7526202607565722 -0.9551685075284215 0.04843015565592523 0.8548254239329698 0.4888436646941674 0.43908656944651003 -0.3710161640197325 0.928336902275771 -0.3890337058926292 -0.8528501508159949 0.20802270506968057 0.2352672352499401 0.6065762957653864)
)
(inputs estado))))))


(defvar *TestPlayer35* (make-jugador 
	:nombre   '|TestPlayer35|
	:f-juego  #'f-j-nmx
	:f-eval   #'h_TestPlayer35))


(defun h_gen792player5 (estado)
(+ 0.39199073904368387
(prod-escalar '(-0.2458765808007226 -0.606439153023759 0.6917972857621095 -0.08386404384603785 0.5165928275423257 -0.17199500624314545 -0.9201212018035689 -0.1728785210558108 0.40150686777282596 0.5354824124651738)
(suma-vectores '(-0.9326829311685827 -0.5831161058941565 0.6506857994391955 -0.8102734840336587 -0.4689650832728205 -0.27259067734217424 0.8302681466111406 0.1401611554828508 0.6096126147955714 -0.32793311800258196)
(matriz-x-vector '((-0.07274429301670637 -0.5610069186840072 -0.43454005466306733 -0.3749156699412217 -0.5298858723742521 -0.023610710617189223 -0.6293292952801719 0.2607733119467617 0.5534356864010823 0.29266540619829606 -0.8851834250648214 -0.6827173615207571 0.1178439181642772 0.231199560876991)
 (-0.9034106599810043 0.2659655891659698 0.2740930474644405 0.8808181087259186 0.8254952048040491 0.27300190206372754 -0.796884407887045 -0.5406265383276903 -0.9613753068268309 -0.3702089434146447 -0.5391012594747622 -0.9241775418596936 -0.07547559817254568 -0.4469884752906568)
 (0.28624047211923376 -0.6743352148202488 -0.5090225229016141 -0.2411251560730987 -0.45350557167498295 -0.9174467655435081 -0.014220285613818273 0.8947431527304892 0.01653035764007904 0.9872245493261347 -0.7589442002679083 0.9211913842418089 -0.0935859304569433 -0.5468949237775425)
 (-0.2603856689174846 -0.3195386554625057 0.05902211452159856 -0.4351750356373554 0.3857899332066892 -0.3867752863228049 -0.5909229771661537 0.7523936959188613 0.7124106232632654 0.2759795718994449 -0.7950726527777661 0.07392337177827257 -0.5995956555374857 0.7540429010520415)
 (0.5312600356552932 -0.008618203966358706 -0.7055887941746655 -0.2815517394323721 -0.5718659727335829 0.6204823964536463 0.7543642556398731 0.4904899746242408 -0.20347832064800442 0.05786508205488716 0.8957721796950733 -0.607284057660668 0.44872032545703266 -0.6887515380987328)
 (-0.6374740034832791 0.4955028580286138 0.3239745937942431 -0.29578957435461706 0.7705774923377144 0.207943608786062 0.30333189267726457 0.2997412252619298 -0.28124023874076576 -0.23585511609272825 0.007312917553762066 -0.07757466765475463 -0.2362891883256537 0.8969989287988964)
 (-0.09002217137004465 0.5406287640571237 -0.9257872555143905 0.3912844902101791 -0.9510587307592329 0.6687318125266255 -0.8529150046142118 0.6575115815257149 -0.8833493115187099 0.8825584875817225 -0.8629305703294794 0.14658445359998407 -0.932292908168556 0.9154770038262126)
 (-0.9899062686263693 -0.8964018018074371 -0.11152589456385287 0.2181424735187465 -0.034878479978904364 -0.9395996689133805 -0.7110479415654463 -0.12529811111044964 -0.5019294525806424 0.4102562076058527 -0.3690406642845767 -0.18062385947680237 -0.5340446306141471 0.7706664550522351)
 (-0.2325463595573911 -0.7355434118396604 -0.5116268818498115 0.1554619625817506 -0.6137976379648369 -0.5865769836249974 -0.2550663920244245 0.9363775648568351 -0.8638263980238301 -0.8341291314699313 -0.40771120982178566 0.8672888138303536 -0.3505173827407526 0.5098416117601461)
 (0.18901207710902823 0.7383390992072174 -0.40731125143165037 -0.8473058159820352 -0.6282896461399441 -0.2345239772976473 -0.9963891854956144 0.7355318036671714 -0.39888420432303384 -0.0845086926173586 0.8682415226424915 0.07942923618855557 -0.31489086871598193 -0.4449525999218642)
)
(inputs estado))))))


(defvar *gen792player5* (make-jugador 
	:nombre   '|gen792player5|
	:f-juego  #'f-j-nmx
	:f-eval   #'h_gen792player5))


(partida 0 2 (list *TestPlayer35*		*gen792player5*))
(partida 0 2 (list *gen792player5*		*TestPlayer35*))
