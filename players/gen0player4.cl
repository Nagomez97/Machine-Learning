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
(defun heuristica (estado)
(+ 1.8546112418892429(prod-escalar '(1.621258375977053 1.385933723086602 1.5240824120599137 0.7530888218518048 1.519873311081333 0.8139092092122631 0.9493761482677023 1.2687796576488748 1.4261153541034102 1.0190800636239898 0.8491456942742088 0.9445790519091932 0.8911792329237007 1.2316415649751224)
(suma-vectores '(0.5025656271880938 0.4560116261244711 1.550814763476561 1.8267207528269802 1.357317769475616 1.3135979174689258 0.4545151796882769 0.5020191119120365 1.6964426920953117 1.6168790835788145 1.3903049285594131 1.945463946944605 1.555294343167306 1.9694935053522122)(matriz-x-vector '((0.0008286838032771637 1.0788799899344068 1.963055889510093 1.09788815872557 1.3082617088879203 1.3787475690559359 0.7870903133302825 0.2812004413109501 0.9972828881777076 1.3626373478939524 0.3111430290694561 1.2217581073595485 1.7865975443556301 0.9324140226350213)
 (0.7451320231291103 1.7691136513382741 0.4914398311325052 0.12568096221170233 0.057706897893218034 1.2694329111609672 1.5776575401795834 0.5186145504360318 0.8818391409563775 1.3065561144986286 1.9596639834682485 1.3841675622253173 1.744059642986942 0.20304337028825814)
 (0.3398198047022516 0.7514828462755279 1.2000225848317458 0.9033052347740052 0.5315922015707646 0.07296938041556644 1.4239325515076826 0.01739875452292039 1.264291351322099 1.1277480978108785 0.7712465891809976 0.15423132535212813 0.5928220281935961 1.650797560113749)
 (1.3544895511477972 0.4287677060095414 1.5967357713990975 1.8073473029454519 0.3114133822041323 1.3153877309565738 0.4217466146304065 0.7504118547952956 1.1883096002067988 1.5665530109586427 1.7581116476254293 1.984002035388435 0.35760632748157395 1.8728469359809048)
 (1.1549558257265768 1.5398845124589542 1.962005404134331 0.18811983266566457 1.775072996780614 1.0441406067781087 0.09362526917387926 0.4905755320864844 1.8661816309863006 0.3598396954904264 1.8103917824733022 1.2685379537695909 0.3486376537905307 0.6224445130688314)
 (1.986339427039065 0.4525317887041662 0.043717798131005736 1.8070471783677855 1.5375404908421915 0.9908859447556753 1.8461353260100604 1.403405692318056 1.0965220000100226 1.8241628651100943 0.3565561193175544 1.3545432516380052 1.8451656094888165 1.7852329857818359)
 (1.977805825925432 1.2351506862331816 0.026909242932567468 1.1024979159514539 0.4586089570625458 1.6083327978066844 0.2023998476078097 1.123875077354783 1.9702991652477961 1.2593141278670428 0.2108044229011521 1.0475096821364807 1.8371677265030675 1.7919082557304893)
 (0.8318439561565898 0.8262300914204899 0.37150755291548987 0.18932040438644826 0.4049591502614651 1.5383313753671632 0.3497815979466954 1.5387683592450898 0.07244772012137402 0.7038838856068819 0.2100382381914203 1.5923731511644101 1.06747738323883 1.8270455852494125)
 (0.10549495173659773 1.6724576883770315 0.8314764931477816 0.7098982708609867 0.6372895700712897 1.0889437778371853 0.6204795917715351 0.7176216072676653 1.3738962036034656 1.253094693583149 1.2414026280284034 0.6145855208851501 0.48469552860471454 0.9481071686803528)
 (1.7213544372215763 1.92177066341316 1.2522495737281103 0.46623084369604095 1.1071867661804944 1.5601696373585523 1.7057996630552013 0.20480468534316043 0.5055161515109272 1.2509975918628802 0.08332384772837531 1.235704116693853 0.9170599673744126 0.741475122732838)
 (0.019135753392869992 0.9359432477894816 1.4661100119950905 1.103274779190323 0.8526221986115281 1.4210031801874075 1.6740712707378078 0.7012813913515306 0.9866360624449226 0.4730316012059308 0.8883761164711823 0.8111683702913393 1.8308000552983927 0.8341228971899224)
 (1.8538104250854304 0.7088386491108729 1.3051965744234644 1.0523148359227967 1.1255780105826825 0.034192685709820037 0.16048051042102318 0.9513337295701458 0.4548808610718069 0.05425901973708713 0.3842405548113643 0.7254207058747999 1.6923573210284142 1.2090315895730321)
 (1.1344743355175853 1.1039111169842475 0.318981251262096 1.8370173167423438 0.5480536395237185 0.1330034783334273 0.9182161530076594 0.15513302617737024 0.498156184367063 0.5250698533063847 1.381820659602637 0.9577991455469503 1.9001417867190031 1.6484827644865445)
 (0.7635561166731999 0.8487318987865862 1.6115496671839902 0.511460118121108 1.3110904209083647 0.136170420163773 1.555220334523958 0.995523898578311 0.6923406618556656 1.6358404385127885 0.04663092966404592 1.971713640611628 0.10540249895274334 1.184157796494389)
)
(inputs estado))))))


(defvar *gen0player4* (make-jugador 
	:nombre   '|gen0player4|
	:f-juego  #'f-j-nmx
	:f-eval   #'heuristica))

(partida 0 2 (list *jdr-nmx-Regular*	*gen0player4*))(partida 0 2 (list *gen0player4*		*jdr-nmx-Regular*))(partida 0 2 (list *jdr-nmx-Bueno*      *gen0player4*))(partida 0 2 (list *gen0player4*		*jdr-nmx-Bueno*))