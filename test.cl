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
(defun h-player0 (estado)
(+ 1.5643506012143291(prod-escalar '(1.687494096429388 1.5889682513833054 1.6508622937404964 1.669249590436729 1.1318972195267454 1.8870094288482278 1.9802280898615514 1.224150539733224 1.0321147731418183 0.5164490193479288 1.3623328762192366 1.1562939863512403 0.5945025484006852 0.5605214469552842)
(suma-vectores '(0.5274906970796702 0.8513185021955565 0.17738659236672394 0.8536226590091001 1.6500334432777513 1.6291604931030372 1.7767295431784416 0.10983558083574252 1.87745603656835 1.5757320719951846 0.3228594016096449 1.9161318483290886 0.6932104221535629 0.13092853682382732)(matriz-x-vector '((1.262218862100314 1.3863999447137063 0.9702019036213869 1.620735822918085 1.8646807842402884 1.2429075099601603 0.8182407742922264 1.569378357232398 0.4016037550546441 1.2986024634153235 1.1897933518624828 0.902124461858365 0.581722335809715 0.5753855994033583)
 (0.8376841852483901 0.02774811713148262 0.9564581257235762 0.9262107722772004 0.902053837083415 0.8683181682533343 0.5500150046300583 1.4013506567806748 0.00046930537887024393 1.618444515066998 0.6245920366919968 1.7206791476887382 1.676824943597482 1.9270332612235417)
 (1.5093638671194893 0.4720451610512366 0.18633700812567966 0.08255073626120724 0.21029578559649553 0.4651724715356087 0.6021963417754865 0.2837084159425751 0.6553225913365996 0.6064884918526576 0.43364709342183083 0.09673367921813392 0.6870696850812934 0.6700771094056506)
 (1.4671430755155517 1.9994015564213552 1.200701924522186 1.8195205493921065 0.06335926926832025 1.3436420387359043 1.1634776020501836 0.6945589988931582 0.7280215095536975 1.9220216223528044 0.6198038841427411 0.4994522391093372 0.5706929866947696 1.9781883816094639)
 (1.9501451567732446 1.4317260098894917 0.8827051733590405 0.6250291926573419 1.0947569757730196 1.772837845508902 1.413646912277355 0.3374967846422736 1.9573828624720344 1.806928650110507 1.2852925306263858 1.4054681959341593 0.4798558968551576 0.6861341695150878)
 (1.684662459214806 0.8278171250327404 1.3090022535195096 1.0467632343686633 1.21472726891324 1.3384768482687914 1.4940365004726965 0.5888680268673097 1.3586280686217431 0.5595548185441599 1.5410068998333195 1.3462814426847314 0.20719476360834865 1.379911416174845)
 (1.738438841740839 1.0830905754400255 1.656220552405795 1.5873468200494028 0.8903703777291816 1.264609610237568 0.6231872208273996 0.4209468385448738 1.4304984001971282 0.5710231098458287 1.5490570661801937 0.8563402909017641 0.9859891523033222 1.1053950212305188)
 (1.915866581725486 1.6258197517126038 0.924243969762168 1.0809390511684218 0.6750368615900211 0.7014851441272978 0.9587836296587664 1.925542036392328 1.2422059505281553 1.5420676622139402 0.9984338923715843 0.17291214816938472 0.012547235454615446 1.3478806808447743)
 (0.9786041119084974 1.9919150558152576 0.511783919337744 1.626996505906042 1.9915746443206408 1.482438123420602 1.9996464896463408 1.2762666934821196 0.8831876984456679 1.567099575760551 1.9731538512404982 0.05643037934801676 0.0402637472790377 0.06480697457993201)
 (1.7414465906332477 0.6913994038451863 0.4576814420987734 0.13990381574768485 1.6189756351856461 1.0273986212336863 1.2054496877074339 1.6294715139487272 0.9922741994429876 1.3422045461389431 0.14601391385592044 0.3238637099187609 0.6564736418293278 1.5862990347283605)
 (0.7685258868853915 0.05195287200152676 0.7894957336774535 0.4512252195774049 1.6327800490696176 0.22565787556820238 0.523229596972185 1.508845472212727 1.3793586563512752 1.9496510030160077 0.6108022375528852 0.22412242568804053 0.9284212514316026 0.005968677959687474)
 (0.7192378935469013 0.6725859637274882 0.8626171993179368 0.07446734749137796 1.1008527089638314 0.6136709542787941 0.5689164038501862 0.17322989639475095 0.4433217155034943 0.6604967157777648 0.26394717055350103 1.7442481051982661 0.3891607243397115 1.0919578207867513)
 (1.5288715776954376 1.8811305839457826 0.5220747405336015 1.1930813769876398 0.18640310177584185 0.6514568523316362 0.649791450072498 0.676746472698377 1.5600027535652494 0.7616699793686534 0.6437116969561465 0.8985495753773702 1.7139304136796802 0.69728694082724)
 (1.4160624911554025 1.5858312368974923 1.6268457505977905 1.4117334068045182 1.24311827985518 1.8689304517626686 0.04585097970025398 1.9270389735584856 0.8869567489285286 1.984564826100588 0.4663998853722864 1.838048336104632 0.7422481776700172 1.3966674325244377)
)
(inputs estado))))))


(defvar *player0* (make-jugador 
	:nombre   '|player0|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player0))


(defun h-player1 (estado)
(+ 1.2520113786948588(prod-escalar '(1.583004867444267 0.225353032569644 0.5035576828026633 0.6256177508039458 1.6141171011056499 0.7611079166277492 1.488758233458014 0.12568590145562908 1.0959708905294185 1.7484178206140626 1.058231892768721 0.06602722660114879 0.1565947352002861 1.1248669272044767)
(suma-vectores '(1.684480205706657 1.2241118688304744 1.022577881146818 1.4057978852551467 1.3216769851777757 1.6416157959281836 1.0753297112868525 0.39773172569497683 0.8914945117520594 1.1320695207086606 1.6087412606896507 1.7038907267348167 1.8443893539745468 0.32289774163739016)(matriz-x-vector '((1.663596157434232 0.7572376899511593 1.700084051534013 1.4135406434155944 1.1834935031131764 1.943519008448385 0.5008581108839725 1.8581990022234491 1.6601087369432534 1.3784571729959798 1.1200231798113505 1.8966370591757504 0.6318891870028212 1.1872909039386217)
 (0.5697195656996805 0.7913178714075477 1.0626107272243879 0.1247846140318225 0.9681149306555494 1.8110916740648604 0.3517968670601772 0.9872583964877593 1.10819756971222 0.6145235970221083 0.49242478099363063 0.2947374116771244 1.5134580619137252 0.40483470800953136)
 (0.5996927622210722 0.9253500590569648 1.8360586268469201 0.1450683407947 1.748806522909017 0.9104275949797895 0.2808382338461861 1.955017904598379 0.7228953996649452 0.8750801790261027 1.8951223947605498 0.7348708992216075 1.737238052144634 0.08284322868020122)
 (0.3815457473376247 0.8064971481475709 0.9948910892909495 0.12548682127850408 1.561833111755244 1.2146996255230575 1.3428286810207546 1.9610061403361911 1.315479526416534 1.663507508531305 0.4362448221224047 0.30394022025721723 1.5608226241202716 0.7789367196391614)
 (1.951255035996011 0.2677885430090783 1.1916511757047108 1.5464355737067865 1.2034909020218274 0.08266664620333009 1.1691614887407098 1.3019703699808847 1.5288331115344973 1.9260744167119517 0.2665163354598723 0.5193266964785337 0.5223403492272534 0.5170180354078568)
 (1.5887593771011004 1.9832978079593777 1.6717370022747722 0.1831766992739432 1.177532384119844 1.875900922206814 0.7925994704612063 1.744552555461076 1.2474300543512482 1.3729727574582584 0.21102722975149169 0.48537571349560804 0.28804181384094996 1.9157425615171009)
 (1.8214976201721782 0.2958653148058241 1.1671825869995776 0.5428923503748113 1.7614109421307156 1.0628117497598148 0.8212004225443503 0.7056293047136839 0.9452030790878758 1.592577560524598 0.14917353768822195 0.6385924663842575 0.36763227334025506 1.5619494393122773)
 (1.2539863993088198 1.7495252327295006 0.9042951649014108 0.7841273004504237 1.7245643873858951 0.9711965307777437 0.7813667324981668 1.2942005133186227 0.2351188930729866 1.6258557724667706 0.1754404258022768 1.527075352138474 1.404977273885842 0.895002702879127)
 (1.1100322574662482 0.5840242284892452 0.21979531179412803 0.6651158159442208 0.7382557907578 1.0463105476340535 0.8364582700033978 0.8872215581055041 1.178971418304647 1.8895479686351027 0.8201178781476568 0.14564007363532827 1.771003556001718 0.8827096024654351)
 (1.323683779308864 1.7242519647187093 0.43658260151492434 1.9363246850515596 0.24649160315854446 0.3594148720951915 1.9701131829947338 0.16522682580496761 1.5182356263031223 1.216292168770337 1.1974510814397337 0.20168063918789159 1.752932945219312 1.814605997275741)
 (0.6778918136044936 1.9693721844956815 1.2321300797710835 0.26730176008578077 1.064653390425501 1.8676100602047907 1.5901989620593924 1.0188412401216371 0.40225853814623447 1.8850556398227711 1.3862729389786683 1.3330749609029893 0.18089419800340978 0.9848308503695471)
 (0.16114538656311606 1.0544790076799802 0.7132754042914933 0.1687846689924335 1.3201769881741288 0.4990382877639623 0.2561310897748452 0.8306267038431328 0.12904101960448844 1.7257881632915526 0.9275841487518386 0.1028933269101342 0.2648433776330421 1.6569159196438432)
 (0.5484605337808184 0.4762746362108641 0.605478200804253 0.7651831360629926 1.948723486830245 1.04527063438699 1.0507474370726773 0.030511112009734775 0.5339061506116485 1.211512709032088 0.4685413589392169 0.02264290642615152 0.367948152577775 0.8806821773885838)
 (0.19864525110149378 1.6205209387086903 1.1296645972561676 0.11810070718615284 1.3074027904137553 1.4782940065202093 0.14808887936273463 0.9625560008565694 1.3570736548079132 1.3048907938148349 0.3168063172667006 1.1424195088568103 1.2278466257120981 0.35415217324340653)
)
(inputs estado))))))


(defvar *player1* (make-jugador 
	:nombre   '|player1|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player1))


(defun h-player2 (estado)
(+ 1.2191570810223982(prod-escalar '(1.2368748745503213 1.1832269498147208 0.1023223706784655 0.7953854073728566 1.482556647397141 0.12397651156076739 0.358834907445549 1.7263632336302697 1.6149412238167395 1.8321486142562715 0.6199855086593782 1.9874900458868894 0.5545516212187234 1.3900375692125087)
(suma-vectores '(1.4992101678556307 0.37529479961031376 0.5385862753549435 1.6620173165592675 0.5005794716253911 1.6453123390077145 0.34640486132991843 1.2846460720854083 1.4283292444418896 0.2979632182592127 0.6779654492766247 0.4133980242223134 0.2270652455007489 0.9134773376549101)(matriz-x-vector '((1.7497741960670903 0.3967853085234849 1.7239196376776758 0.9533858153861237 0.3629270864729741 1.7556042498494278 1.2892558065645723 1.5466714442103404 1.255330890787978 0.25761051583517824 0.6848655767379668 0.9200938868023874 0.695457427410271 1.3828440059116818)
 (1.626644449519206 1.583813680682894 0.010797593504222824 0.577452311683297 1.6329317683151636 0.20548565866122126 0.9908769970043487 0.31654788340664 0.3798384169259281 0.7588194522306748 1.5796353650582797 0.7941012752406709 1.117220724406955 0.606675069126849)
 (0.3253282646218507 0.4580316547754286 1.7017113119008496 1.3518501130846883 1.0374146301352294 1.2226805818014475 0.7184636661519963 1.260962864761476 1.5834174375976602 1.3418993004457502 1.7997440118750796 1.6251902257897952 0.964324373310381 0.7363576457743848)
 (1.2161885044388636 0.4016779965099626 0.8582963255646254 1.7091650177181215 1.211370705208064 1.2275312675420322 0.38459815485721704 0.8556039362638206 1.7253489375756275 0.1226335623140471 0.3315604022401266 1.936518964795462 0.0004548016366257013 0.29397159410974694)
 (1.4970177633505255 0.46841486895896 1.2230000931302623 0.22912533874370555 0.03757963990573976 1.7982882056862364 1.135215128018637 0.38164527091393885 1.386870011912293 0.9712282353769146 1.1468075693497015 1.388138695647634 1.7969782511924022 1.8158761175551406)
 (0.9005770733067842 0.7595144867526324 0.22634031798000454 1.1385926333865621 1.5304759550280074 1.8578832979609359 0.03569748773717496 0.83586584897969 0.10832299752456698 0.7682355249628194 1.0024396340114718 0.5799287222626415 0.8707988376011144 1.0603207497223996)
 (0.9843391389793501 0.9332973880951692 1.1551066204970017 0.5340577903897641 0.5365406943761724 0.42786872172353885 1.7160731135820164 0.9915423993438255 0.5444086806986237 1.7219707356480303 0.615877137961411 1.1908189048868765 1.9205646660206233 0.11575643704963001)
 (1.1090279282580295 1.725628972255887 1.617157614991573 1.1054841825105006 0.5814315614606202 1.7628889001550114 1.5832523208345777 0.589823408544417 1.7854882996986063 0.40392936652146716 0.9136174833947666 0.543015094839522 1.9027808467381448 1.4892018330246868)
 (0.31815259394022033 0.7959391365236459 0.49709206266113903 1.4374244058976728 0.9789219160945164 1.2718878038360912 0.6402640192024271 1.6616781371357254 1.5058618836432185 1.556973235296636 0.6606857586318455 1.3538361520883861 0.5260322074357586 0.15676008840810018)
 (1.610530909349964 1.596958807258486 1.0913371580236892 0.5840787115312251 1.5023181856261942 1.413315985530874 1.3992407452130116 1.875859063127632 1.2636213268554113 0.26105489487869016 1.0140635839893937 1.754903323709445 0.12943960161081436 1.5747389023155962)
 (1.2978513066145438 1.4610020379426318 1.3305906032369932 1.395704404315067 0.9854315291404994 1.3403365264668594 0.7757733504714914 1.6480735149175403 0.2044293937780346 0.2728288638445753 1.017351936211829 0.12268368443441857 1.696018018045867 0.37510980371314195)
 (0.05704696900149786 1.8260967258026037 0.5611506324377009 0.41924806069845566 1.5882610729684488 1.1437773764457468 1.5385597197941867 1.6980755788246942 0.7876058623539595 0.27380916493036644 1.7508779529622118 1.5324883010168606 0.22377199815976234 0.4382030305353246)
 (1.999110635578388 1.1143395682331303 1.7943617763157993 0.48153800255625145 0.09236381499254276 1.83758404684521 1.3152149706352576 0.8617606841746828 1.429610222597892 1.5399784680851776 0.8350287220605292 1.475052626271858 1.3159794312881916 1.7405456845239113)
 (0.04942695580965051 1.4580186549617369 0.5678944659625227 0.19952865545307352 1.9312448666043485 0.0405562930047656 0.9648931917083832 0.6953231111712841 1.18670388004634 1.1285503090023166 0.2780201994102858 1.9229966951804294 1.1741072994134156 0.48867789899557734)
)
(inputs estado))))))


(defvar *player2* (make-jugador 
	:nombre   '|player2|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player2))


(defun h-player3 (estado)
(+ 1.39032805883116(prod-escalar '(0.451625624653748 0.4640686663876836 1.136870372496165 1.822297379752276 1.4104514498085952 0.9126203081018691 1.252332322888275 0.43859340452718 0.7054028287875267 0.11319809032715322 0.20311829203909815 1.8762025047905775 0.2576054043578053 0.6005360254074392)
(suma-vectores '(0.21861974864472655 1.9470945642636412 1.5991559115733227 0.45212837561465924 0.576043608624679 1.5542314714870205 0.3512144855640005 0.8811217402017297 0.1801164021822752 0.7571353350581362 0.20876891536311826 1.1629867087356998 1.86169272236299 0.8949539916899985)(matriz-x-vector '((0.5509942701211412 0.7518634007739695 1.3652061543214942 0.1451273037494556 0.2185317007376042 1.8188582285019808 0.16000967195203142 0.8954833500223212 1.4339720133282736 0.3879299279128283 1.2653713281007306 1.0040297737811779 1.689457389525709 0.442679778422409)
 (0.74864663782402 0.41778979207152167 0.47553156752163406 1.6652141672254912 0.42105989729972926 0.3134711437967337 0.6983904287722396 0.9174963537530376 0.18464043311447242 0.9755544491783734 0.2757621420339109 1.9735959331381236 1.5611725676914607 1.7105770959000042)
 (1.0901910172033875 1.5264212711780432 1.6295133994586573 1.8764456734291979 0.003084332010075519 0.7219279633760456 1.6237142604130017 0.4757442149859672 1.5745790521839442 0.9436415116801138 0.7681868983766591 1.0393057814712887 0.4995439955466461 0.6216237526651716)
 (0.6714795456889657 1.2226548764782368 1.6359924461092328 1.9419218741261661 0.20439763366645392 1.8604069695364016 0.9775295717245758 1.2107215950732884 0.2730915305756294 1.2927100503745435 1.9834430089874078 1.9069241200861118 1.4317797763490945 0.32854438324633684)
 (1.2308340598561904 0.6014548902659387 1.9209705538052686 0.300585162241086 0.1342482725070817 0.07147884303970287 1.8561713519010012 0.6928906386762159 0.9350724710187224 1.2293881617096252 1.9933392607564464 1.6364276579897354 0.031812171457158644 0.7902155004632079)
 (1.9923544216692581 0.32658701321448835 0.41935972259885745 0.784757266433286 1.813322133029245 1.088111939893071 1.6531503207779528 1.1173052925949805 0.9571797699771769 0.45017331855765286 1.0258147742669912 0.32139395257753445 0.5201627773881079 1.3520426828119299)
 (1.1371102614748394 1.7437834879611573 1.3069604964189543 1.1401847760762593 0.6002998485832372 0.39251842006085136 1.3535285017193952 1.2868096915419758 0.024951586394432068 1.237311984403128 1.538308864625425 1.3273064403406754 0.068541260028679 0.9023661704737889)
 (0.4737246964391719 0.5090063587973446 1.0146202759128664 0.9756894371812328 1.6623882004770707 0.7934992642724468 1.979099961595124 0.19485356158431189 1.077268313561804 1.1630953409024714 0.24092183849132764 0.8933835920983291 0.4393562876433321 0.5924920642120848)
 (0.923490941876995 1.375209646196675 1.3576293586649493 0.4309722140286525 0.6234501895275657 1.3524694644447153 1.2396508530965133 1.9646918566929763 1.2880583804875807 1.6304444912035758 1.789316867703551 0.014769646876100273 0.832462128645588 1.3918079514226873)
 (0.9740612424119792 1.8690704556265925 1.2772947885320676 1.126825214107906 1.7405571823259949 1.9374798141268663 0.7254045043135593 1.08144336097585 0.5686929862330801 1.0187298791558717 1.1075390070802413 0.44655240881852665 0.5582462352262174 1.522228990082844)
 (0.3240684774514484 0.4609654012118538 0.606757829009934 0.8667563138402308 1.9852513269712744 1.9012115900159814 1.3516718359716775 0.20547149653915953 0.5079809650070288 0.7644939642323119 0.8725615271547822 0.2562266550430734 1.7333157116775113 0.8948656128702355)
 (0.6155980471229809 1.1521378409975978 0.803987519169616 0.6178633321607319 1.4572760655170984 1.2532357961255332 0.6559397592444691 1.9241605300227722 0.9431525687547067 1.7377904129786013 0.16631520576960201 1.1901391240504728 1.927631339950324 0.2489132149808122)
 (1.3492237233884066 0.2650988703886936 1.0240604501270827 0.7335070660534864 0.9411998389693708 1.6028368052250699 0.369463832574481 0.05397209038358586 0.05448545737697641 1.2200983081214605 0.04008490597238512 0.43645449692796445 1.8669901577996033 0.7295040544667657)
 (1.048424827503386 0.6316897528765777 1.5519859377339666 1.1716744843759217 0.8916102054045769 0.4388075709258119 0.42813191285109986 0.5004984580677423 1.4857506095128339 0.29225171636043945 1.7200806723974111 1.7590245458163078 0.8444124370868618 0.5670981135262649)
)
(inputs estado))))))


(defvar *player3* (make-jugador 
	:nombre   '|player3|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player3))


(defun h-player4 (estado)
(+ 1.265466016965938(prod-escalar '(0.043199447352896936 1.6560879340904373 1.6184069222792763 1.215366271908335 1.706734296559265 0.5007289851242829 0.06382125710413233 1.4938801145644691 0.052991366574971055 0.8430975473457711 0.9306200614835114 1.287889263444646 0.7702214573848531 1.1330714334286667)
(suma-vectores '(1.3215761137952826 1.1761582994546096 1.2790088499949759 0.5827214064757404 0.500409686391978 1.1794724318580696 0.8633641446132159 0.6597671981168558 1.7404229815231975 0.38100464509118726 1.9918825597349459 0.3840906853379529 0.9098656885885827 1.7171546085879867)(matriz-x-vector '((0.521020099952902 1.3306329884489794 1.9491298839526832 1.3678194449125114 1.4552835309120247 0.005881711427883518 1.5082139319407843 1.9891726063884871 1.9981123981676745 1.2063900123021651 1.9774910135482222 0.11961726521771254 0.2197406594572915 0.8683647820861)
 (0.6711655037522037 1.4205885124145623 1.721370103066364 0.4602539741547995 1.8338249140095844 1.3914664288495138 0.33295040275419163 0.7028531194175309 0.6665352656722705 1.6625764152383447 0.2178314594665105 0.942052162304901 0.9977969603303452 1.1000940925941975)
 (0.6225304282829582 0.4080392807048985 1.0043443698549621 0.05161064870121934 1.9472279434203552 1.3017550407969811 1.9356124613742762 0.05167157482179663 1.0795047254493655 0.6580882437982076 0.12488307615378291 0.5861887452411008 0.6977671019166416 1.7007865430263243)
 (1.4134418541870566 1.385963322221579 0.04894658794366813 0.995054367593037 0.5260507758008868 1.9724340265857252 1.3600064140896162 1.008197720766893 1.6642747172998842 1.102048998386231 1.1350139219412219 0.5070916351536217 1.754788682660978 1.3693406089082605)
 (0.05495758816776686 1.8402329434697218 1.782369666344867 1.9613114031723267 1.0680525093578974 0.012278347211242657 1.1683630369131097 0.5114138711520968 0.6429196773705512 1.612799783188655 0.8829158771031382 1.389452029539342 0.9678397582721778 0.4366966219471524)
 (1.7913409627345516 0.18384712037585005 1.5897257189355327 1.1436949493815396 1.0675270553942355 0.682263640548793 0.6143703753042655 0.220221071134018 0.6425171342714191 0.025534760403668866 1.082857455408541 1.9381025328339796 1.1919265037797233 0.3216989813897284)
 (1.3325056180735448 0.6905195464500227 0.11863496307710286 0.1511885321546449 0.0051891437240931815 1.1485226395543464 0.6417308952623164 0.2765883937407465 0.6705844316547782 0.49014131122120674 1.2133266991511455 0.020220178381924026 1.0416679032703562 1.9685701649034215)
 (0.8870913983176645 1.8734979881475826 1.4514799936414753 0.6268219781260738 0.8663605949146607 0.33512689780402183 1.157646873832083 1.5665954527028383 0.6520981074512475 1.2593480329043836 1.3041472141227113 1.040853554374523 0.052872030475133114 0.5536073655702274)
 (0.3943578659774054 1.867000177086028 1.655571367570959 0.29928599694864966 1.641362528412198 0.9354083016390751 1.6483787333059585 0.8673846903720019 0.5730572842090529 0.3396264064957213 0.9473518486808838 1.672798165078973 0.7183760852855205 0.65163017098784)
 (0.3622550259341224 0.3162476066735278 1.8728971933628258 0.8105181943402833 1.8062645065106167 0.0038602487522534368 0.6832886251297194 0.34507941944646703 1.3359994622442768 0.13982234262660054 1.0654667384545289 1.4936501417166212 0.9742923253546534 1.1513744340348628)
 (0.44823825574606 1.3125495055505303 1.2581763149709908 0.9760822407783298 0.4019841589932698 0.13413961097945992 1.3240911126964399 1.4831061691208345 1.8522861389872762 1.934084380785584 0.7805714755242423 1.3851529267778282 0.4915878809233607 1.4762362281845802)
 (1.2458422763510602 0.7834679406960625 0.8119977801759983 0.37189010886204876 1.8791834932316398 0.9800243412330236 0.918917331289137 1.4336493363946359 1.6814921777644094 1.5870599753551964 1.713132348680305 1.7374029736315821 1.2520533407229524 0.07287864966173307)
 (0.3554812797755047 1.8896762165930574 0.7826966932313244 1.101349939729094 0.238189317447822 0.5438806595769752 0.8740725500128259 0.007596265437015193 0.16508454457326516 1.335204744544111 1.03813153588027 0.7734378692447836 1.7408120633171495 1.1527153161885557)
 (1.9642135163307957 1.9395415366171005 0.41742782725062 1.3382182050771456 1.8402702773283934 1.7517408824507454 0.28249444923418277 1.3224652852319936 0.5297067150949066 0.96109428505078 1.88268448019111 0.11061134887073032 1.641896679184001 0.3923531035475061)
)
(inputs estado))))))


(defvar *player4* (make-jugador 
	:nombre   '|player4|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player4))


(defun h-player5 (estado)
(+ 0.5277389461435518(prod-escalar '(0.7884487942554692 1.4773638296864164 1.068146203492686 0.1083317744466934 1.8371940762956969 1.569033369551058 1.098279383493685 0.42635963967089885 0.24386393116761962 0.5567752595046853 0.2021501256473166 0.6003629561362758 1.0329008011413983 0.06913281040086416)
(suma-vectores '(0.12112140496339219 0.06828923772027662 1.6427700474460907 1.0294387954963766 1.662682165031066 1.7855070702852973 0.052224859748142505 0.38168122079946354 1.7715774322678943 0.5969240701323981 0.026354874796573613 1.6699552952030063 1.5045735341364044 0.6981900466174422)(matriz-x-vector '((1.6298405259696465 0.7136159306985086 1.5593209261849883 1.1491724936288445 0.9373512933269446 1.7034733167631626 0.22784543681525848 1.4996307228833536 1.7437111120007447 0.6452437802285074 1.341822534134593 0.8348464076866922 0.8095456323004049 1.192249799079103)
 (1.1728502140004453 0.35601486084676104 1.386342706351258 0.9929825098908742 0.23944546057231064 0.46678105674188264 1.1811132339438029 1.0822067346443378 0.8590999071302221 1.9521629397319433 0.30073412096732 1.2492292562633305 1.5765071525607646 1.20608404462581)
 (0.57686566828327 1.9408871032316057 0.4489692199805102 0.9572178910723503 0.8724984676916623 1.0858103299688262 1.679821304189534 1.4769872887527458 1.2862601593398124 0.1912000749751983 0.9322970246683715 0.9329153778453334 0.15836130908802026 0.2898354911881209)
 (0.8857871799227643 1.6664249314180153 1.1976009439791486 1.2437560277347903 1.8995635224711096 1.830996467600595 0.27606094891217947 0.4860444082098949 0.8257696099393657 1.6146805213812712 1.862036434343672 0.5938515228657815 0.3518028416249819 1.1065944798491096)
 (1.7882958499434323 0.72096557664064 1.8381235360559987 1.420985295561456 1.1814022022966078 1.2629484720314756 0.7492651238612109 1.778613854741736 0.6415110468996879 0.6899446004220167 0.7618542912445834 0.2648430957293739 1.5662803473521016 1.7436342706760768)
 (1.367432217913883 0.7802282996441012 1.3710448873464476 1.9507475162310015 1.3789541870336812 0.14768070089227914 1.7710119800153779 1.71496653363635 0.2665056780214585 1.1579967757900522 0.38036433688309 1.7189343571288123 1.6026771566658509 1.6871470419653662)
 (0.59829000790166 1.4212937680934168 1.0280238252849603 0.6737424948151491 1.0896974387919607 1.7440738512028537 1.6191499223330732 0.39426229371485655 1.3500558230621145 1.3768176978043625 0.8434927854896157 0.6249056043976875 0.21328180409996667 1.7646786119965439)
 (1.4342649654145627 0.030333640321920763 1.2552121246087518 0.7018457223938936 1.2072316818897142 0.36793787618644713 0.20334176006027826 0.6319352866795958 1.7145853931228296 0.3941654890378221 1.00384995691475 1.3567197116383676 1.188493753567494 0.44136962041582595)
 (0.9545877204412168 0.8723869538001106 0.5220252045702083 1.1870271004071162 1.9284255553547043 0.2155267746364753 0.9693126896085336 1.0344250093547314 1.9089416664766607 1.8754020736917103 1.6404334454884162 1.5941188281005205 0.8366396826049947 1.5765469614142642)
 (1.0184736199602282 0.9552750013478755 1.5676338441681035 0.17011537521405984 1.2294503778584331 0.7794807246009436 0.1864667246505045 1.375689478610592 1.6605973359678532 0.025939092347432524 0.08743325745141828 0.65261670929652 1.741249828598815 0.338038645705657)
 (0.3798697822259087 1.6463875316146694 1.8811021572935978 0.614158765463465 1.5782924088666535 0.5746733027734117 0.44546248946871114 1.4183026881988963 0.8059189210215425 1.7805261846247098 0.2908624689373349 0.5276227904866093 0.9333222356588351 0.30057357359668324)
 (0.2142767021488019 0.004514602240289545 1.5412832344939202 0.1590148483460132 1.3037654227445747 1.482255014092867 1.8869539969959808 0.14723074065258257 1.2408522238645556 1.645601109347489 0.45674201866859265 1.4246526404574709 0.6105732915041415 1.5403601102384064)
 (0.738077090106219 0.6345019818419342 0.8399053845094007 1.6117490165161845 1.7105054097103116 0.5759508987938848 0.5850288147198566 0.37176922475228746 0.7103084072954515 0.8959977174660718 0.7693318690947386 1.1145534068121112 0.3766799379207877 1.5626057947788767)
 (1.6026395888322946 1.6667817014855593 0.10979238304087446 0.28993512070600613 1.6325565404508309 0.4534209398037128 1.1289812558253614 1.808076123457155 1.448929079913558 1.8552637267467607 1.5773826949174157 0.17639988760474012 1.9045544892112019 0.05542896554665222)
)
(inputs estado))))))


(defvar *player5* (make-jugador 
	:nombre   '|player5|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player5))


(defun h-player6 (estado)
(+ 1.1492813508560331(prod-escalar '(1.0563591866713382 1.3261259371430538 0.5288003331132594 1.6430532432441463 1.1575782692657273 0.29373859482981146 1.456924236391174 0.41912311344204856 1.255786021567472 1.5714487596432276 1.5772988877629712 1.3674220279748537 1.5496598999070779 0.30506412271812033)
(suma-vectores '(1.1740559796509624 0.17849370909207773 1.984248627720025 0.12690014245419334 0.0678878107539671 0.5101723878222657 0.026512494087074012 1.7459145080658163 0.668183669401816 1.9849603739682737 0.27436079949442393 0.9131404149712417 0.24124156767896898 0.4733639447316713)(matriz-x-vector '((1.2967812060431165 1.722513587848173 1.643660876140568 0.6046044548795686 0.09017474598331199 0.5458130992287495 1.661545325980574 1.9878941962309555 0.48082745399682225 0.7940297557062326 0.295534544969424 1.0075394376265507 0.5482019961751399 0.6536031902262287)
 (1.3919126119526637 0.05785486013229435 1.2789745317271177 0.6172979673809234 1.1719338077803256 1.7675478440200605 1.5616512228873245 0.19475730182762252 1.857630664396767 1.756648414129826 0.2802850890824329 0.9050519551159257 0.4232202938256566 1.25131768579293)
 (1.0486155211930572 0.8131878724193147 0.1227449048076692 0.15571250674233084 1.9695088389892839 1.6433776301434815 1.6962415259981198 1.3751515721103371 0.7420945401322399 0.13025183707128174 1.5950061160122826 0.39713858020329895 0.47208943181894814 1.36579037830276)
 (0.39263810687233724 1.7274825764214297 1.9724397965319047 0.7384010418163649 1.9929044207961217 1.451061647053657 1.3317624254255644 1.9474206293475054 0.1087701466978277 1.7594915610718618 1.5860797135405122 1.0582405921307332 0.9705928505571197 1.5939993219514594)
 (1.124173092230599 1.4887975842610395 0.7538354708090806 1.4099824644060792 1.7469407391422966 0.4581243488570559 1.4635489704058446 1.769182633012774 0.9424336573329934 1.6285823657202076 1.5487531883716061 1.2198560031609575 1.413859900437965 0.49589379079835827)
 (1.9690725998894691 0.26347310297796933 0.09547210311161924 1.4460684733420117 0.07630266895407067 1.437825490763925 1.8284700073531643 1.1322147774521525 1.766547443021067 1.6465399139713817 1.9993346062653878 1.193392303639136 0.5246580225255462 1.3664012013606914)
 (0.49557069474006576 0.02001664152474203 0.5722334588625151 1.351170681119204 0.35727414376134425 0.5375163261794687 0.4931264362144838 1.5112599932815152 1.9111991676330204 0.4113188849017455 0.5700647704731823 1.7102115101813977 1.256303107432102 0.7218031890807215)
 (0.9811513868015043 0.02528488697075093 0.8823628865235884 1.537762363222568 0.8286672289852257 1.155631794184729 1.0500209482072242 1.404594198042113 0.11978944256026702 1.3557958533689634 0.33786873124718175 1.3760408828709612 0.6891023922113242 1.1036545265841637)
 (0.2376798431208671 1.7314214772505963 0.04045888297552325 1.2346655682921608 1.7657575533984171 1.7842371399748902 0.49943749936143433 0.2873926657382089 1.576227098108845 0.16318891651187384 0.6401120106885867 1.9279280899153584 1.6954246252061054 0.043690859254117864)
 (1.438998613485085 1.5798796910605146 0.5470219691109981 1.9030639592054037 0.6315444619965687 0.024707309410474387 1.2695513752434822 0.8897642464754643 0.16130055446964486 0.055009552178481025 1.4078499039496437 1.4671110036908004 1.6766871558621086 1.0575224857355887)
 (1.4023327155010532 0.9230030599763857 0.0031184797252379326 1.4875917195234383 0.4939039212585923 1.4717481349303068 0.010346269648556117 1.9589473953932974 0.8246546570407771 1.9101679726393546 1.532031089253512 1.987585627743293 1.79168173745526 0.6269152841929329)
 (0.14423041031057893 1.5337350367472056 1.2641044167988824 1.161182810936044 0.7702870138345053 1.63915576815143 0.9939432900428735 0.8702287770036514 1.6440668706511516 0.38208953379542887 1.1503513344798768 1.9342850485734604 1.2521914409024097 0.5184759951907663)
 (0.46138535089158506 0.3195547721802179 1.2592999023999687 0.728807324746938 0.14466373364796636 0.5386514293067468 0.514533778873429 0.4129816414725471 1.2853979887301354 1.7565591532052787 1.306577733440222 1.852728952662534 0.9712825728097751 0.5682680924131351)
 (0.9097669865652034 1.5751336905580913 0.862496118980085 1.6876612677514968 1.9634446392563942 1.098000296702068 0.058985281462693884 0.18217028421201498 1.9877493942232738 0.927575269826761 1.8836339702013662 0.3101332314323393 0.32840762601845763 0.06848495550540878)
)
(inputs estado))))))


(defvar *player6* (make-jugador 
	:nombre   '|player6|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player6))


(defun h-player7 (estado)
(+ 1.1590094947591165(prod-escalar '(1.1529750397825815 0.029788200642876905 1.0848906525902384 0.9742509293739299 1.5309481146234125 0.43163041882360575 1.738137764698093 0.06935258319356707 0.286515114056469 0.18144617705614796 0.04324264833124092 0.2205245967019991 0.07105097628517965 0.408338209815968)
(suma-vectores '(1.6229368177236472 1.0421358453952334 1.153491714026676 0.7480945092460889 1.585537085495713 0.6315728661980105 0.5056499561742231 1.7315145823264841 1.3124770299074648 1.137465345454094 1.7950062701265808 1.828023208046409 1.7796190434230923 1.9758579387723056)(matriz-x-vector '((1.1556225885804707 0.8087386852014464 0.7572373685113398 1.1391644520596569 0.27557091793689503 0.6780728764457877 0.17411486566504464 1.5022388311613646 1.8453948902980288 0.6031250627651596 0.9205927224079273 0.4565682518246281 1.535885010499651 1.4156649839338862)
 (1.6165475247704673 1.3769474063721396 1.2231128552315824 1.652911054695256 1.4452468497959703 1.1422570752683026 1.7562324489676366 0.46407648661186185 0.946044737269707 1.9680234648779216 0.9779832167089706 1.120188778415604 1.72746310096083 1.06785509405394)
 (0.9813390160595479 0.0951384679871119 0.6874987188312707 1.6127923458303033 1.9473818684429538 0.9588030594087318 0.22233396318876952 0.537621345032133 1.335827019513568 1.1508201675155463 0.3779356462651189 1.7945752332980196 1.4924550265100407 0.6458907053396157)
 (0.5464856689898656 1.337442662393171 0.11802416988346542 1.7454799782832517 1.3795681986657384 1.3879226591204983 0.496461509686543 0.7320833009716845 0.1383582091699067 0.4693046582963467 1.1235238164100818 0.8207067521438607 1.233508761511274 1.211661562106385)
 (0.43529953558920154 0.14030993076940557 0.6773816104621622 1.0701073805389867 0.15560128841433252 1.4065462105860553 0.007022431332914358 1.3801925270690552 1.0759353941831207 1.6417335239326214 1.1284958206150317 1.8227581275796612 0.6945220184097902 0.8580666778405592)
 (1.1930744275703629 1.8686930251990015 1.481488469851658 1.2847973617728394 1.505524885489804 1.2753342014818767 1.9755750187386263 0.7045991088562948 1.8610273520348526 0.9898850769840919 1.4592255124180256 0.9591471486218603 1.2891673499455525 0.5231402531788045)
 (0.24690165265613206 1.6603490235463465 1.6781854611136986 0.3667509557156323 0.9371372098598676 0.3104139169291771 1.6029855369418995 0.7355140716412651 1.1412943918402152 0.8177062481614212 0.6174986455864082 0.4070609703967889 0.8740805406450731 0.8297688819090987)
 (0.5271465999495326 1.538445974626742 1.6503671794503192 1.9004353155491212 0.3816518640612039 1.2618276876561667 0.923499819005263 1.893470218094731 0.3913785579357665 0.14503641899795783 1.7171748847002677 1.9439322418694833 1.0722320162018963 0.5032821201014355)
 (1.2323171773592954 0.876609467877701 1.143018749123801 0.8329475762589631 1.7545381791611856 0.015017686010328823 0.644192489188639 1.5110697399923976 0.3539196611886801 0.49190248597478625 1.748730851180204 0.4975800819019345 0.700873298364799 1.4313100841515844)
 (1.950613072201843 1.540042836435007 0.05904572332011693 0.281382029862828 1.3146271365870688 0.8240748511665394 0.011785231977262445 0.5095967991111059 0.8174566632564388 0.10650026604577745 1.0684414361795151 1.8085117499747738 0.6870275461619855 1.530314312072872)
 (1.2591730120670832 0.4826327811464257 0.22116491353499868 0.46512616007416385 1.6057969603959699 0.5038090863654945 1.4854165006202584 1.3281656286708656 1.482549439509911 1.5845841448280213 0.5101745285683299 1.7845837587702162 0.3263532207483193 1.3219944823151564)
 (1.2599057655792172 0.105276778621193 1.9511298615417614 1.9876585281890558 1.7572868259581618 1.560572327060665 0.6028282288068647 0.7744881782515698 1.772901701233489 0.8101124448553372 1.8979501255053188 1.4355370626897512 0.41855085940086934 1.5010998055872398)
 (0.7554947761833086 1.6289363465462685 1.3803010804419342 0.8961486017815077 1.7676572017269687 0.7072189314071933 0.5738491182552747 1.069789338488943 1.9040870547253146 1.9754303406972418 1.9742172561712406 0.39229141600891704 1.7164391016075613 0.027938153087378348)
 (1.3030549051653233 0.43548223752073323 0.8939785011123562 0.07370270769086629 1.6097589147592868 1.9553746066195354 1.6434887125276805 0.4693716839043651 1.5703417071609618 1.0622168777353775 1.2158074738457907 1.797708772361708 1.4650193204506787 0.2679465259563678)
)
(inputs estado))))))


(defvar *player7* (make-jugador 
	:nombre   '|player7|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player7))


(defun h-player8 (estado)
(+ 1.0014660285653858(prod-escalar '(0.33877485596793666 0.4189387657722181 1.1663569442125692 0.7163392829030744 0.44046279382264286 1.3876369471855163 0.7802645908486261 1.050153026443079 1.2807197971841355 1.917098705217669 0.8470924693632857 1.077745014685577 0.6738019909785624 1.4053659223388508)
(suma-vectores '(1.0111825599907818 1.1982546280438118 0.4110090303740257 0.5134353770570677 0.9434788071594629 1.5765957108780602 0.7275609634888938 1.5870223306549212 0.0016759135134216674 1.2783494346981716 1.7673103614148582 1.838225020001196 0.07538772181572662 0.09753174941024301)(matriz-x-vector '((1.9039349457725516 0.5764802537632705 1.7209626638328386 0.5346229338925836 0.9272845978246105 1.9342532210038554 1.3691626749118138 0.6581693703908735 0.610893177213961 1.5077701319995087 0.04314215669704513 1.9815051665944354 0.22855138159066057 1.6604805201664297)
 (1.3039377022578678 1.6456775633803853 1.5328116157533294 1.4622884005774224 0.4745029110926413 0.8098011294995371 0.008411935549107463 1.7117809192889688 1.1086223949105372 0.5971075397625605 0.038650747515943884 0.9039472226957375 0.8561755933146711 0.18051706294614545)
 (0.7840354012929918 1.632551094017645 1.907428519888952 0.11752033236469894 0.10664372128092592 0.737165840459906 1.5803226404242672 0.42309125314510077 0.5867604419209849 0.48744779575039554 1.629948041738804 1.7034414644551008 1.8256656589200388 1.4751154428156779)
 (0.04997476244853605 1.6013495830256215 0.7295532652972221 1.6372129288364834 0.08400944178186665 1.0841153242953592 0.4516966053339251 1.3374397236615319 0.4603403726646127 1.3379263054243427 1.7623394425451142 1.488221817396782 0.4778203593381196 0.20506944222932888)
 (0.3359813861388137 0.20248221579838943 0.5045717580316669 0.09654999632222827 1.8820492742775041 0.9941708572815471 1.3997774511425947 0.8238677859768131 1.8643114787965644 1.3354773579581327 1.2965635543877767 0.672214764264299 0.7806686662672717 1.3026242078913837)
 (1.1747599841451928 0.5983416319330728 1.6743898899910297 1.5146513196529934 1.7690622861607663 1.4382157860521083 1.707400286889342 0.49460113425485885 1.5013370717542813 0.396203256571352 0.6830014731798428 0.9738457566777374 1.1242334958683176 1.4582460138498066)
 (1.2343588113036492 0.030027541900084387 1.609003396885508 0.8213840481584773 0.8428345426959265 1.6730615717782795 1.9141009553471127 0.2818608975567174 0.17944715910986297 1.061274292445637 1.8910172032302632 1.50892218780128 0.9250322120359857 0.02960356277131937)
 (1.62630622971498 1.8789667833261485 1.9004413285349684 1.9766416553501267 1.9893032505951822 1.0390788639106254 1.497291209373078 1.0136996006012422 0.4966753057945441 0.916233925230368 0.46554703051354007 0.9235340284606712 1.5756586397621064 0.7202524891115694)
 (0.1854380328493448 1.9013045078495656 1.4153137254875767 1.5834934483188667 0.23043259914731262 1.2755632883774732 0.8482213850556874 1.5031894536930437 1.8272170201259765 0.6198340035674812 1.5086395574035023 0.20824924631442676 1.4106346819879814 1.9590396584763063)
 (0.3459318141545751 0.8664066963689123 0.3583547139783758 1.310655421288047 0.6635062146848794 1.0827847641200279 1.8440789715367087 1.2013940569619121 0.3948375450607169 0.9986523825285143 0.9009236939255605 0.7290905615555283 0.9441575335745487 0.3010907708018693)
 (0.05034565177700068 0.40645541196141566 1.2703181361365743 1.749087554226684 1.2622597504994948 1.1944603720681668 1.2879980678350933 1.4020618211110298 1.2986007456413633 1.2833033862475847 0.6813440412596077 0.6765123692109518 0.7482825418191206 0.33976220844575367)
 (0.14115930501556218 0.8659575673465094 0.8348852163874307 0.2783885389288403 1.2876414722452154 1.4723086659032334 0.5710877686364608 0.07589777710991785 0.5709353025011654 1.0976345370993126 1.9337966473395864 0.42422440522431537 1.8500801575673778 1.8071895059981742)
 (1.8757151364429276 0.26963980210604976 1.5890173787516038 0.14775370353957484 0.05374773737715888 1.6681871009532787 0.9888672347961664 1.3035528916379289 1.6323211385775378 0.5813375336612636 0.4342787084600317 1.8030704961451633 1.4953041449997098 1.4800961685798932)
 (1.149253043450565 1.0925771236207298 1.6420140169155537 1.5556189216629817 1.1818262022575274 1.5483147075294246 1.6743767680677053 0.6235585392468266 0.5337242481672018 0.24482458713187816 0.7764674590218708 1.6715590321001361 0.017725882428261786 0.37916640114215094)
)
(inputs estado))))))


(defvar *player8* (make-jugador 
	:nombre   '|player8|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player8))


(defun h-player9 (estado)
(+ 0.8100119383845972(prod-escalar '(0.9837043577964513 0.8856498617504687 0.045809586311670314 1.9005386279106369 0.6368324670991081 0.2854792464093783 1.524718741780917 0.8223028439209097 1.781859498063232 1.9914787129978513 1.1353128267746078 1.4926592230939157 1.863687190169513 0.7234908966741038)
(suma-vectores '(0.18964615392214812 1.8154328427893707 1.7487684987527037 1.2841057199068568 0.29385907383657717 0.3237685971633484 0.9985331296606217 0.4965789070399993 1.2256052315857533 0.2215535942832565 0.3310519282403743 1.9968153762125558 0.03706247104788307 0.18840173992993936)(matriz-x-vector '((1.1837808414722764 1.6744285636301488 1.8218904422479485 0.25559368398905646 1.2161142688344102 0.7099684577522565 1.6171279949146766 0.4985954128003329 1.1561376591509303 0.3432949845966464 0.7634148599851214 0.09547530159911655 0.3486717195194464 0.4302837295882218)
 (1.3480649763856403 0.2851577792781992 1.2113085253489628 1.2248932932754328 1.7107503151963939 1.1089808453311603 0.17882878241865874 0.22692503746496917 1.3301351585993184 0.9970826795396315 0.7911269388378719 1.8194959626065588 0.1053873700240684 0.5007373327003501)
 (0.8480681452394707 0.17726668411028146 1.3943518189888815 1.9850152310339664 1.004505362163074 1.7103699006846018 0.675605049457277 1.9090517979446817 1.8771375380858295 0.1439285902806029 0.08812134975044339 0.8954172040805819 1.960341886296646 1.7476885675261022)
 (0.8225694013222111 1.2729352196387314 0.9824661859384873 0.8090717733887944 0.9589401055994289 0.20732821213196106 0.31705627719926 0.42735288048838793 1.6255082897858726 1.328667347525717 0.5804258514471516 1.7254949041264096 1.8101284322706992 1.0311329015378794)
 (1.8060642643590068 0.8905313713496064 1.8498356985443707 1.222722128764603 0.19183693893957954 1.2252270096474045 1.0691320370808417 1.2567361838169009 1.7548047355021679 1.9562874601915536 0.01294320776092528 0.40684659470422346 0.6136642643493009 0.2716572935693349)
 (1.4490005671495791 1.8472059168936221 0.023964578783033597 1.830610978803337 0.37825217063758076 1.6031961898041416 0.85263026188766 1.6784705319798563 0.804663336102545 1.2093156010576693 1.6833719571214059 1.1789795150364377 1.2727572037452854 1.5744682425512555)
 (0.4733007688079427 1.3687596843421763 1.4518081051107228 1.6973329573205638 0.26834311037023006 0.4181350489109361 1.9867912700275414 0.08009575311307304 0.2345038185230881 1.1750085851311005 0.6154284748749559 0.41226390759122955 1.6606559640030991 1.1917807949651884)
 (0.9858411151866526 1.5105358134730587 1.0327965548701976 0.7571611116201773 1.0865452546423673 1.373176752439361 1.5828534397342942 1.4585928613606056 1.1602511357958687 0.8930627275058578 0.29851390208645867 0.4197335806016482 1.6274047359982602 1.4336365056861837)
 (0.600890658967818 0.12979413268186124 0.06712714511675921 0.2693584132558908 1.1374640658340742 0.785241388041036 1.9282546191741678 1.5796005718426616 1.541296970742053 1.1829503363905733 1.1993022578207837 1.4331195525622766 0.5082487275017509 0.654566871229844)
 (1.0743028061970776 1.6972588201772276 0.42096733783604634 1.870546020219251 0.4719640242765599 1.6959361856271693 0.4522738540895861 1.340519979435433 0.2046099965546515 0.9884031552544237 1.6367208608322323 1.5539545764682505 1.0972941127729248 0.373135163228129)
 (1.7168874921881958 0.7958425671140104 0.09631064892660923 0.7846266474568409 0.6995599400760881 1.6376305088408483 1.4443213094560414 0.18787281689436264 0.0348306159487215 0.6185289544865706 1.2404684829516603 0.5110078607976372 0.4088367682737153 0.34821231423355137)
 (1.8926866623854588 1.772402523395114 0.5493422090524183 0.3353860893741172 1.6141742588847607 1.4263169809138427 1.1116060975452766 0.7440980349706674 0.3445767043731818 1.9594475851247735 1.499116467908363 0.1464403396927425 0.09294802586995243 0.2981023504150204)
 (1.6020160725755044 0.3832914898338877 1.0534654507261672 0.8076105477046358 1.2004630644639063 0.08096660716942639 1.9846307156917162 1.7443969665896066 1.2873951154887096 0.7933373893854176 1.3018393840824312 0.621333830700975 1.1966805680138124 0.4680512483460626)
 (0.02927753271829525 0.13139591514850446 0.16843345447108726 0.5578947749458751 0.614395342121719 1.2822134059245889 1.8479518547147147 0.3306939469817689 1.7645040665602967 1.2538477777417067 1.4376362979187425 1.806268557458726 1.0378655956096177 1.2010144832839156)
)
(inputs estado))))))


(defvar *player9* (make-jugador 
	:nombre   '|player9|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player9))

(partida 0 2 (list *player0*	*player1*))(partida 0 2 (list *player1*	*player0*))(partida 0 2 (list *player0*	*player2*))(partida 0 2 (list *player2*	*player0*))(partida 0 2 (list *player0*	*player3*))(partida 0 2 (list *player3*	*player0*))(partida 0 2 (list *player0*	*player4*))(partida 0 2 (list *player4*	*player0*))(partida 0 2 (list *player0*	*player5*))(partida 0 2 (list *player5*	*player0*))(partida 0 2 (list *player0*	*player6*))(partida 0 2 (list *player6*	*player0*))(partida 0 2 (list *player0*	*player7*))(partida 0 2 (list *player7*	*player0*))(partida 0 2 (list *player0*	*player8*))(partida 0 2 (list *player8*	*player0*))(partida 0 2 (list *player0*	*player9*))(partida 0 2 (list *player9*	*player0*))(partida 0 2 (list *player1*	*player2*))(partida 0 2 (list *player2*	*player1*))(partida 0 2 (list *player1*	*player3*))(partida 0 2 (list *player3*	*player1*))(partida 0 2 (list *player1*	*player4*))(partida 0 2 (list *player4*	*player1*))(partida 0 2 (list *player1*	*player5*))(partida 0 2 (list *player5*	*player1*))(partida 0 2 (list *player1*	*player6*))(partida 0 2 (list *player6*	*player1*))(partida 0 2 (list *player1*	*player7*))(partida 0 2 (list *player7*	*player1*))(partida 0 2 (list *player1*	*player8*))(partida 0 2 (list *player8*	*player1*))(partida 0 2 (list *player1*	*player9*))(partida 0 2 (list *player9*	*player1*))(partida 0 2 (list *player2*	*player3*))(partida 0 2 (list *player3*	*player2*))(partida 0 2 (list *player2*	*player4*))(partida 0 2 (list *player4*	*player2*))(partida 0 2 (list *player2*	*player5*))(partida 0 2 (list *player5*	*player2*))(partida 0 2 (list *player2*	*player6*))(partida 0 2 (list *player6*	*player2*))(partida 0 2 (list *player2*	*player7*))(partida 0 2 (list *player7*	*player2*))(partida 0 2 (list *player2*	*player8*))(partida 0 2 (list *player8*	*player2*))(partida 0 2 (list *player2*	*player9*))(partida 0 2 (list *player9*	*player2*))(partida 0 2 (list *player3*	*player4*))(partida 0 2 (list *player4*	*player3*))(partida 0 2 (list *player3*	*player5*))(partida 0 2 (list *player5*	*player3*))(partida 0 2 (list *player3*	*player6*))(partida 0 2 (list *player6*	*player3*))(partida 0 2 (list *player3*	*player7*))(partida 0 2 (list *player7*	*player3*))(partida 0 2 (list *player3*	*player8*))(partida 0 2 (list *player8*	*player3*))(partida 0 2 (list *player3*	*player9*))(partida 0 2 (list *player9*	*player3*))(partida 0 2 (list *player4*	*player5*))(partida 0 2 (list *player5*	*player4*))(partida 0 2 (list *player4*	*player6*))(partida 0 2 (list *player6*	*player4*))(partida 0 2 (list *player4*	*player7*))(partida 0 2 (list *player7*	*player4*))(partida 0 2 (list *player4*	*player8*))(partida 0 2 (list *player8*	*player4*))(partida 0 2 (list *player4*	*player9*))(partida 0 2 (list *player9*	*player4*))(partida 0 2 (list *player5*	*player6*))(partida 0 2 (list *player6*	*player5*))(partida 0 2 (list *player5*	*player7*))(partida 0 2 (list *player7*	*player5*))(partida 0 2 (list *player5*	*player8*))(partida 0 2 (list *player8*	*player5*))(partida 0 2 (list *player5*	*player9*))(partida 0 2 (list *player9*	*player5*))(partida 0 2 (list *player6*	*player7*))(partida 0 2 (list *player7*	*player6*))(partida 0 2 (list *player6*	*player8*))(partida 0 2 (list *player8*	*player6*))(partida 0 2 (list *player6*	*player9*))(partida 0 2 (list *player9*	*player6*))(partida 0 2 (list *player7*	*player8*))(partida 0 2 (list *player8*	*player7*))(partida 0 2 (list *player7*	*player9*))(partida 0 2 (list *player9*	*player7*))(partida 0 2 (list *player8*	*player9*))(partida 0 2 (list *player9*	*player8*))