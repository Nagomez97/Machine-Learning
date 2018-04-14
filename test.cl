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
(+ 1.1742964663687538(prod-escalar '(1.5960295128806594 0.039633990282541554 1.4428317886860849 0.9312618486346786 1.395808412673647 0.022441408199447288 0.7153652754779165 0.8786941474676773 1.8218810291893506 1.0430112057748868 0.28707895183483445 1.7761906906450662 1.2751290124664578 0.10332525266495529)
(suma-vectores '(0.559222655944182 0.32724934628320934 0.2774172286697456 1.132157809868808 1.5218538477370995 1.682554143709958 0.19067419611509662 0.8247526249718997 1.3341240409013266 1.075389123166658 1.5333726942019958 1.5797025134945546 0.2561842668943519 0.21032514815346826)(matriz-x-vector '((1.2460530775511711 0.9764281869793632 1.0841443221846871 1.6333303583183063 0.3901734901561651 0.5390306808539631 0.8065100254126731 0.5823356762660128 1.1364642191452294 0.14509096903573648 1.652783054813745 1.9289400694605066 0.028605643845224238 0.6462767464131696)
 (0.943973329917708 1.870479916181165 1.0691674888602842 1.8592251591195181 0.367091302293596 1.5021071626655245 1.441809797305596 0.1188975418879683 1.1253346759618157 0.034971510870108746 0.6476969095384595 0.1615200103752692 1.1895109585568633 1.799808502211598)
 (0.5707953644569834 1.6576232802679636 1.0930192595527537 1.7605288359862 0.90144236180254 0.5017513990294253 0.688286377852757 0.4252940501295597 1.9468962574302688 0.9002838258618797 1.1114060676683708 0.5380374329639686 0.2426340958519715 1.7359962590449125)
 (0.5987938666165828 1.3605058606775111 1.905791249536553 0.9852669658158155 0.7429207327640028 1.353882313204435 0.7178245054889119 0.6858131218346484 0.8475970752066997 0.7099122651744096 1.0950831305869762 1.2561220034352596 1.3417800420265151 0.8630873687981386)
 (0.17814972093631942 1.274711007472041 1.0857474486279226 0.807447938905969 1.8131267652244414 1.6197692847103335 1.8063744982273697 1.1568749392225162 1.0370039528310788 0.9030038557804201 0.6278825400355728 0.8863726301492183 1.9663366684627117 1.4664460037307616)
 (1.5941168164740793 1.2993926942453187 1.9588218264551707 0.14619696138579563 1.7285868034963292 0.04965948739122039 1.9169447061726044 1.4182109954447262 0.22150966624471846 1.3694838027234906 0.24806763449074043 1.9745326600033086 1.7176455620226212 1.7571109598910237)
 (0.48886624789532784 0.9874571321421579 1.5001066532211271 1.4760594724937925 1.6226350367716917 1.0814096483126547 1.135774321140187 0.3968584318816957 0.03733757220454126 1.1713338987342752 0.8860307684916415 0.14049083654308192 1.7246435008796084 1.3338382707459087)
 (0.19524306254549328 1.1398147556066263 1.336963881916845 0.4600424577638289 1.1871017173559453 1.9044295046351163 1.827574525800703 0.1494532143559122 1.6793471467326204 0.2142164743503192 1.3803976202511485 1.1317850584538849 1.7557452113323186 0.6844898471446712)
 (1.8601196491295797 0.3233149135003057 1.0042867414680212 0.23453719713999588 0.329506198848853 1.353104474645683 1.96842700216903 1.7177880457557742 0.7967022725615962 0.19737649935406387 0.3399595392601069 0.05669706223067705 0.24172577515952254 1.9065971696777746)
 (1.9702768069495227 0.6179515681363001 1.6998428500573795 0.7655516778549727 0.7481097812099633 0.9324893784215265 1.0103599450687404 1.52280207776599 0.9221681964702786 1.2246819849694708 0.7697064909212818 0.4370905243304952 1.3939118408694642 0.9030942264688031)
 (1.3976665010275766 1.934709123982433 0.22844847814945135 0.28219181332630927 1.5100989057901593 1.1672825698911875 0.9961248074854925 1.8416888233563253 0.9764119629777768 1.879743046127994 1.4638827294853474 1.4690325087958231 0.7349117326470338 1.0631927713618674)
 (0.9273588019593737 0.7875448406269059 0.6328704203065798 1.2037127573324784 0.9721341393064307 0.24152326008207314 1.426016843377939 1.4510030595254455 1.2437478126293022 1.5520293583034854 0.626944296033292 0.49390496895664704 1.1062663702024917 0.7355549616638064)
 (1.6329412185876122 0.56369128531336 1.847768595856104 1.69377725928576 1.2963488353736783 1.4548529275811521 1.3601314382533227 0.4444107532560544 1.9236144095355443 1.2610723626586868 1.2029612402952488 1.2811050906488315 0.8634523497197084 1.7219477132473784)
 (1.728571970271883 0.2627982863668634 0.5528288286273781 0.6133531799067276 0.012356713135657671 0.3944231498379498 1.2216633300920765 1.009891395461943 0.645153651331583 1.8326668004194204 0.0390235713743976 1.6464047888763578 1.2860506503049858 0.6798527010273099)
)
(inputs estado))))))


(defvar *player0* (make-jugador 
	:nombre   '|player0|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player0))


(defun h-player1 (estado)
(+ 1.863627487251932(prod-escalar '(0.9811455252356458 1.5313412226191299 0.12335316724811585 1.5634207352599523 1.3772854276494029 0.21217639851825787 1.6086004673227268 0.6307093343503163 1.5535897989343443 1.859687200550733 1.3936788644709428 1.2701641788679405 0.4631477474555239 1.8910904191214704)
(suma-vectores '(1.8513359620227345 1.6231191701176175 1.2445196238476308 0.6919894447341752 0.7325956422262239 0.9751755629388934 0.45235877450133155 1.1014707039895995 0.29507891186524904 1.2720079864977059 1.7851835241562177 0.9206925308037492 1.8778266320536703 1.5178313164891977)(matriz-x-vector '((1.278841528251956 1.1191531249800934 0.2332157795489862 1.4815008232784785 1.3625002985125627 1.801936634772819 1.0842740747284927 0.9505871405619892 0.7487163823253051 0.7640024256673634 0.6200018823118891 0.27052287694128796 1.968139168416698 0.6585174250747405)
 (1.9626709765998245 0.7239611429374921 1.9308880373124948 0.44653490779290417 0.1745391784485415 0.09177015051013182 0.28771136966242294 0.4685616066982543 1.8230709593222851 1.7428073111230569 1.1605391854874054 0.8777978436953675 0.8664922762271112 0.9708602571691913)
 (0.10844182393047097 0.546854398254079 0.9452720532507046 1.3122667117155122 1.5868156334914163 0.238749266929017 1.6688004838385901 1.4066840658426887 1.0144714454558525 1.8244060011276357 0.8524796770099579 1.6229646995161249 0.9865698426433669 1.9308391120209527)
 (0.6092201485049253 0.5327713571816926 1.5555340182803485 1.7926075891824838 0.9676179497181627 0.35735481163674687 1.865707463495413 0.5772876834123677 0.10052437557590355 0.3501084534349823 0.11448250286209238 0.5724052307561489 0.2733322534737055 1.2421963501854685)
 (1.6968549451305666 0.4408033498340771 0.8384861704122029 1.8756841663633186 1.8353783843317548 1.249213325549525 0.7547596064239972 0.7679336113320601 1.6220987342655637 0.07354727836053443 0.19698243120944414 1.124022792645011 1.7985051574222795 0.0066698815597439065)
 (1.3920639202223186 1.571634459536017 1.2288562234908995 1.8231313936523612 1.1170441588094198 0.28411627709979803 0.023769078757920337 0.21229668615002772 0.8920204704893402 0.752983167030985 1.1158823693243203 1.2246404727180469 0.44779238875844407 0.3298164830772907)
 (0.46531746925098516 1.3169221209763275 0.2700221260521678 1.9864908785189883 0.5540680320659495 1.2310945372729043 1.9604428917574388 0.061402898690870344 1.8078729421004573 0.3222876367076617 1.933469758031036 0.8100705830729915 1.3992734943597012 1.0352226041624617)
 (0.7295902265665752 0.048283360629776784 0.10870598372133045 1.3347639275709984 0.7701166060708373 1.3906555608059374 0.11721299006226316 0.9870056664277671 0.5381735774543537 0.296751315123867 1.32431793313645 1.6984121170250317 1.6361958695370538 0.06479477005059087)
 (1.943926576556824 0.453579436094139 1.1488042791797208 1.4532455764436842 0.6219025735160775 0.7717949191305271 0.08043053583243198 1.3239798441574377 0.4998501526697354 0.9543594752956839 1.3786416717249037 0.49342638154153873 0.18094347480945916 1.361792572851258)
 (1.8481220584225262 1.600519759145067 0.7521390775326666 0.7110802207656914 1.4407028867366927 1.9680493152820233 0.9631273225812624 0.27567328116519496 1.5721763357164007 0.21834679029349235 0.8405045518801373 1.9150916794412645 0.027522827847285214 0.05401830402776686)
 (0.6517681626350009 1.0303975847026932 0.024632928026461887 0.6206403052494154 0.21669096432357327 0.14172483926911816 0.347121440907445 0.43040228418654825 1.875794170925545 1.2696146289013848 0.2984070062392201 1.2313900713519141 0.639812355617454 0.8291215151210358)
 (1.1563383036867754 1.9488110630244877 1.2071889204508184 1.0269785650133734 0.27644937072971243 0.9002163972851116 1.4586646403827332 1.6214582582699881 1.428404117509803 1.6818721620194075 1.5289613836506848 0.25318626593039073 0.1526260245094475 0.1396375573362354)
 (1.3346502265330848 1.329094228686781 1.4375870148507228 0.35388556786449565 0.031742694568072105 0.890771422343027 1.6445726772495308 1.508685247221883 1.7153992177246171 1.3892479684920125 0.4670742703493038 0.8890459998324602 0.026208518965477712 0.6110611878701846)
 (1.913928704539728 0.77710458275475 1.5759003138437464 0.45733832972247623 1.8811372909531052 0.429137559752754 1.1485007747701241 0.7143202943072544 0.35802945217588555 1.9035489223963198 1.568233991880522 0.15681356088574505 0.41039417260789035 1.8861591608552346)
)
(inputs estado))))))


(defvar *player1* (make-jugador 
	:nombre   '|player1|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player1))


(defun h-player2 (estado)
(+ 1.5610675437507957(prod-escalar '(1.3466714502673298 1.7226025096326019 1.9035132755108912 0.11399043186709101 0.20240874327849068 0.38226485619834305 1.7013365021650653 1.1884251202469764 0.5722413969702111 1.3383173644281932 0.8792794075850565 1.440684458642723 1.779538963836913 0.2446315585736245)
(suma-vectores '(0.7816834789501723 1.1337970235647485 1.9470971319855974 1.790954230246582 0.9308037817115764 0.6849038495652395 0.1297931988198333 0.38584943927354143 0.6236333151191076 1.0259298115772784 0.11388984736973007 0.1333158803594059 1.5911167748805422 0.28940241495296304)(matriz-x-vector '((0.1045643024725349 1.8760774833864926 1.469749664414434 0.979870329034751 0.76960910072686 1.868882980982533 1.7685271025919198 1.1143450890176658 1.7934733770776985 0.6072550576427445 1.0607813309928658 0.7712163081369359 1.5783287316181365 0.8977535364835356)
 (1.8599989306168234 1.427835723521207 1.8352508758460806 1.1365087720808174 0.9054304816735377 0.015315333869052816 0.8132936007880218 1.341783900254041 0.9302873284763453 1.5018711508832423 0.3121479312362141 0.23632652408510868 1.5363880904006146 1.8559055881813704)
 (0.27670280246249335 0.7749850994324923 0.20658228965089576 0.6262169158348112 0.045541155509861486 1.686212850307109 0.3730519496504934 1.7520961850973134 1.3733504849004718 1.8674109894955129 0.09831213168739428 0.026243001503301056 1.8922131301769387 0.7419465445796773)
 (1.0528096761850083 1.104604224180798 0.2772555102954042 0.4882287164791299 0.2073431345086938 0.48448860879114486 0.9367737978753208 0.3573334109830737 0.06802999959981437 1.4995504940741649 0.34358650572203353 0.10923294805954131 1.3517591944918725 1.341625978773358)
 (1.7164738602644642 1.6593707685909482 1.1043426032378265 0.18259942847025235 0.8251551585741312 0.9983864472313819 1.0515083357005663 1.7215330902232024 0.7106696581646894 0.23976187241102753 1.7522123630323478 1.4738600010194276 1.876967100952369 1.136377944537667)
 (1.5893649833206396 1.0653925767859236 0.6594117904178458 0.04486782746318818 0.4432048960692052 0.2767538714284776 1.5246153471135455 0.03511008561656204 0.3964945357357852 1.342092024445611 1.6493143336796898 0.5280253028028039 1.558860162115336 0.8205184153370348)
 (0.24484369604572898 0.012044465648505476 1.3763829333856832 1.2248487774583334 1.0268342097907894 1.295736947826877 1.3391991220165465 1.6807932766518083 1.4501560972615597 1.8536525905532018 1.5834358785008738 0.9425102968039338 0.8044731861431911 1.3902325917694252)
 (0.4850589392450866 0.2793411480710437 1.4345386194934746 0.10719304044068911 1.7359054354960475 0.6252102852278354 0.4617616590181448 0.029743955321707594 0.37174671248908053 1.662496497535735 0.46214912054695656 1.397093411911038 0.452534521636055 0.9357372685086602)
 (1.0344740368044558 0.7124993286569477 1.059454151439942 0.5550771715701486 0.03031252014971031 0.944434019001986 0.859556116436105 1.0494837356195243 0.27149399431017596 0.15706912015383256 1.1137731561493884 1.7527485768799642 1.7406382556136852 1.7990605813285123)
 (1.4545414749407795 0.8198393786588278 1.147734184897911 0.7905277233553822 0.7218185874741769 1.4607859472324214 0.4143514054528492 0.11164167252496449 0.826295511925115 0.7098531060512141 0.21837088617316813 0.9883965326859683 0.1297066456713869 0.592160006591097)
 (1.433213146222737 0.14842921041676882 1.160427781750318 0.548134340946659 0.040528117658981566 0.2424885302912354 1.6014728378690073 1.469275994779224 0.008395414532416545 1.3082557742680396 1.2663047101304303 1.3235377125420547 0.8955623133070836 0.16264206336302323)
 (1.0576551097001907 1.2736134708976168 1.1916622693037968 1.0258925705840813 1.804655222940921 1.2688884171814605 1.3086239203494485 0.21681226365863027 1.366479470580281 1.8816608142279023 1.6841380912180126 1.205290432165298 1.2327442977903347 1.7470492273315514)
 (1.136998864016478 0.12738454893775852 1.1223037493382337 0.8400492461921611 1.1387757556831204 1.457422789506869 1.1254391334662415 0.19500938028668635 0.579803707401146 0.5740195203166776 1.7397956442994835 0.6961103272905731 0.311207712160378 0.18901590563976955)
 (1.6030105814276026 1.5700952332003981 0.9431242630054995 0.7749680345627465 0.5207578728282012 0.26117306643809 0.04767068856769541 0.06198064544033577 1.1862826259032286 0.34626446559003266 1.5915997581051287 1.1888799977954887 1.2660114985378954 0.1384050671629249)
)
(inputs estado))))))


(defvar *player2* (make-jugador 
	:nombre   '|player2|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player2))


(defun h-player3 (estado)
(+ 1.5811357499908232(prod-escalar '(1.5739947129107648 0.4101099371226582 0.9774943681032495 0.783904227980114 0.27598155261297186 0.07772339681201124 1.5831682262169926 0.7059313765398403 1.4860602584210028 1.222898375140964 0.2878807775870049 1.6438100843454473 1.611166515120702 0.4386221380439752)
(suma-vectores '(1.961895380402474 1.244202441713166 0.6908039686974377 1.3676536928821694 0.7850961397343117 1.3575814185265132 0.05879474257899675 0.15914237368938067 1.1377098475291072 1.7705798167887916 1.2924227203548153 0.03888121124698918 0.5555924456665797 1.2615008064140874)(matriz-x-vector '((1.29041943586569 0.9579183532103419 1.8760822538501232 1.3755324021922382 1.3174735868461918 1.5441350209912792 0.7095072535380673 0.515278522479631 0.8995535506656869 0.8115182090488566 0.7058907279187907 1.7618448750279132 0.18487431370324825 1.9859984614112032)
 (1.3352243449436016 1.945488381716745 0.7763486995957987 0.26156737387153606 0.2192204921355796 1.143800132369523 1.452476500803315 1.6947944790099156 1.5956572393457062 1.2895085282882115 1.8268070312626623 0.23134056861904662 0.5592632214631588 0.3925451797447237)
 (0.35226450443164947 1.3387488784897108 1.6940281055879578 0.8561532499267119 1.9098715859895563 1.7994755259162147 1.4747749303294972 0.03161864258135538 0.6068661031245037 1.3406372089060805 1.7958600873041541 1.6331972277580757 1.2456687209236854 1.2751090479015943)
 (1.1235442476990762 1.9508465405176336 1.771535323664497 0.6979905605677459 1.1065773046265488 1.8280079190057932 0.5829501018523189 0.854432074485729 1.5680903274280065 1.8974571628023449 0.5417740483164517 1.655749044083253 0.7048521005987489 0.11886933120165577)
 (0.8793855315406398 0.2421571140120511 0.1256109539822532 0.711530189326296 0.7870774530372626 0.8319818800198759 1.0313342350250687 0.17871025491254433 1.2350781811305043 0.2132717258132415 0.42471110420019453 1.8630722613345698 1.2025878521830042 1.200412537192341)
 (1.440834299550522 1.7820052311123962 1.4222715017572585 1.7094149868760131 1.755469688453872 0.44555485688605123 0.4288090166655105 0.7985549679333726 0.6495576995816799 0.2738953586177495 1.513847070686806 0.6864561330218422 0.7353479123566153 1.2750753870844873)
 (0.4052256693645788 0.515695009414364 0.2731974939076307 1.2673184299534366 1.3095368641491338 1.5276859409820158 1.1644274419141205 1.7242977751339383 1.75364827586639 1.9829654383801618 0.4708591774525275 0.3737196842313706 1.5936743244328866 1.3339259489669562)
 (0.8089103696846713 1.5683112468133942 1.2993140279524182 0.7667165151085888 0.7832996824355651 0.13244824479363992 0.946911561761101 1.7253503776516135 1.400323281190733 1.9390592048010982 0.9934795042772842 0.11429620450536393 1.8715015623109936 1.4522731816238563)
 (0.2760258434011569 0.6009651767626407 0.40566608952303684 1.20667245338996 0.3420719517886621 1.0411513728795232 1.8461409068981005 1.900380971467997 0.4588730797702696 0.7650110562624384 0.8272617445799495 1.2647376046990446 1.685545472698704 1.317265040594503)
 (0.42371773565578796 0.5279685030599965 1.314271666250338 0.5660560488562716 1.710565052872427 1.9918821470806434 1.562878780916932 1.4113087391677415 0.8837989417776786 1.5885591105784083 0.9505470460553977 0.7716883969322852 1.2598563303645602 1.7582717963498042)
 (0.04384958531980532 0.20908941363085765 1.6339145676394293 1.7974808771269348 0.7020026038794787 0.6257869512872216 1.3599057153619862 1.6540991173050446 1.8012088620950615 0.9585563451307213 1.0317905483825964 1.126355922724643 0.92092200425656 1.7782282353454284)
 (0.6309091973558487 1.8156569846483515 0.06575403281705006 1.1670898124277622 0.7563604505416512 1.4562156760545832 0.39873375509447984 0.3017315628442776 1.990632628344302 0.40622145625626427 0.6579711980481098 0.15653842523450456 1.604044229402132 1.793494077501253)
 (1.0384598774862597 1.8835104394041815 1.027050246010636 1.2952240317030348 0.15232423734684497 0.3047470493582627 0.6272058868243477 1.1267557967952373 0.8586101468358078 0.08527750071290519 0.11266905304734576 1.4869166307968422 1.576588909572318 1.0236326868580903)
 (1.4568844908557879 0.38712084289631066 1.0519928444370081 0.8594658023862312 1.6939687681622433 0.06302909521259226 1.4575487840475674 0.18609699571119376 0.06900215800466158 0.02255976364968615 1.8126999026680015 0.276009946175215 1.4923133869136593 0.11799211494718298)
)
(inputs estado))))))


(defvar *player3* (make-jugador 
	:nombre   '|player3|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player3))


(defun h-player4 (estado)
(+ 0.42341087610193995(prod-escalar '(0.35113506738709144 0.01748573001576803 1.5322989195924819 0.947957419275169 0.20994662353200466 0.2721084157393334 0.8725504218746585 0.9593608315604951 0.9490102643514493 0.9643904207232297 0.6035357334221212 1.2128497639517928 1.3850600766923429 1.0896386678608818)
(suma-vectores '(0.3496330025022205 0.14354899733504745 0.039297922411190234 1.492418110235186 0.4829421881466651 1.8108883795813588 1.481988470080047 1.5782516291410724 1.803132127285278 1.937353614706226 0.21451491076068474 0.75488068374692 0.008500259150818534 0.1733138669693397)(matriz-x-vector '((1.9706335077326176 1.058568323226711 0.4563202226754288 0.539142223039877 1.7194380140377095 1.046180458890394 1.2719213021804527 1.8360033097346784 0.939890709571439 0.889644718328777 1.6510482003194107 0.1128124962946051 0.5916478781851509 1.1690385050222496)
 (1.5510089468994774 1.2678242759001321 0.9946610557054159 0.2228105684212094 1.3387542393523115 0.27733068766685864 1.6048824002983668 1.1286934752264726 1.9975245808642779 1.0102507016294904 1.751117190853248 0.7785053051971211 0.3176282406667754 1.3895060463389768)
 (1.296779624053956 0.610731573482423 0.7929155626232944 1.2083074988498403 1.5310762634307877 1.8389950136170168 0.25995071915192747 0.19122515589854006 1.9914734833807137 0.2501200654515989 0.9686651746056063 1.4852316945619966 1.9411991828999542 1.8847258595099181)
 (0.8054675369152671 0.23419084565415682 0.7831237986666368 1.1693130240165923 0.8142351492859075 0.46081594328032427 1.752802983735003 0.8654088002423401 0.4322013054416891 1.9245267830749653 1.2449062719056747 1.5518260647687458 1.46878983009676 1.9561059005847072)
 (1.4632409313789245 1.3416454437131824 1.501975313285232 0.1504135218949294 0.9687007366144915 1.9332951293194929 1.4670492911795665 0.42630148572648463 1.9556635116675118 1.339836551034711 1.6869636789348457 0.7676688546799317 0.322089448887394 1.4847789794558444)
 (1.0702195001889823 1.5024330348236186 0.27031640679880264 0.45369901510088195 0.05364552525188593 0.7376718471032928 1.0985455358874805 0.2759630294796307 0.4437869126138736 0.3572255816319665 0.46777501833460944 0.45639974061380295 0.7728513770270145 1.1695333313897411)
 (0.2151800003516131 0.8899670479828459 1.7462581369515806 1.2235925562623888 1.9145990891864404 1.1995907516685065 1.9325172478644685 0.22738964538667217 0.4888584210682474 0.13522733190925895 1.6302962565465449 0.8643088198611506 1.7069829694539616 0.9894907159136983)
 (1.1471883410237782 0.9451278386371207 1.034351652022803 0.000599542541896092 1.6664749475973515 0.22289109195700085 1.4291696197498358 1.252761338336766 1.586248688215353 0.38666230456386397 0.6272829125981814 1.412291969107627 0.4852186258286042 0.24512273517243877)
 (1.9474578866391683 0.30281521201356054 1.9398391522584377 0.333110442070109 0.027868045899804184 0.1294616408884004 0.8250035189498681 1.9454878409693648 0.8595185136231971 0.3222495155520877 1.6271189982676586 0.5652721663865055 0.06234669377834856 0.8412460952565723)
 (0.2631624590011201 1.9021513659083038 1.320516573577545 1.5243242042712046 0.5687660278037372 1.0822365944111279 1.0158260432186714 1.0912691110660349 0.021579588250132176 0.7441654839601295 0.3750560101930407 1.984987050197243 0.4567987969482554 1.0417415304624535)
 (0.8739447116469454 1.519839486301842 0.7135826994905272 1.058843734612532 1.565541423137498 0.3410949469824325 0.2488700315795811 0.6104128107057452 0.7233798473839388 0.864061233010079 0.7876664105340523 1.03260038052662 1.8338213374722532 1.5881846465205807)
 (0.5793123772905926 0.029574790494488745 0.37965733248537403 0.7406870781475767 1.2504735302193137 0.41312893933738515 0.8952092615616238 0.3477841609266432 0.999369248147951 0.8412201091872773 0.22778412430072992 1.5397620790477835 1.7546330274518331 0.7033227050391684)
 (0.30917861423025306 0.6469113047344182 0.6917614929549727 1.5049686386148688 0.11217679302834815 1.8910441788888666 0.5205858298273576 0.08544347698675225 0.3527485755553026 0.8861721332303962 0.6592727676678838 0.7758059051154031 0.9216558435140094 0.49429433913945786)
 (0.7083175037497049 1.954646330614763 0.8235498755569759 1.6147527525348722 1.2632236014318223 1.6768454199370901 0.8892167458374398 1.8139586875736387 1.2031232336117956 1.6370837653383223 1.0198063876418417 0.1107673717940374 1.9715575328207124 0.852368932262848)
)
(inputs estado))))))


(defvar *player4* (make-jugador 
	:nombre   '|player4|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player4))


(defun h-player5 (estado)
(+ 1.5930126177443924(prod-escalar '(1.9141280915338417 1.5853242371709 0.30118599553078673 0.5376723335034828 1.0911461863977836 1.057998890508522 1.2886276042374074 0.16916807225660047 1.6560937798731528 1.1786877409475527 0.25344033796911125 0.13712125002229003 1.3832038273268352 1.6313376331032012)
(suma-vectores '(1.5968024218056909 1.7800208922464593 1.1077597361179348 0.9864773370596402 1.121550137713055 0.5858966326243042 0.4041699214624028 1.0607078858489325 0.9536109421490995 1.8009881851710725 1.7363838119271136 0.8088405896422488 0.08555228884464716 0.2587544488755251)(matriz-x-vector '((1.5267447185868188 1.7260348681478193 0.504663358457629 1.4229487307771551 0.4312710861857707 1.0451712421974255 1.1664293368665046 0.7212300854303533 1.0879198382383923 1.944866560124109 0.393256631275515 1.525284239832335 1.0571453732370422 0.9278725341292291)
 (0.07620462506468595 1.4837424945744162 1.9378632837210819 0.8571811168948404 0.6828567850330574 1.6473107099548525 0.48320057685649753 0.4343289338846297 1.0032880890543048 1.330671803355278 0.5988067417313858 1.5777739530495796 1.1745868864186633 1.1192170164847774)
 (1.6727474419097474 1.868172961438497 1.488348884756742 0.123805718712523 0.5745863189697793 1.458135015778059 1.3030408598988332 0.33250172934544864 0.2756688849229947 1.7563589475542056 1.2512740235070323 1.621689216378046 0.9814924990534024 0.11254046099299786)
 (0.46081764893407073 0.6302492099636487 0.09960040399147085 0.6145901585234876 0.9897670737973645 1.3103125449438096 1.4856904772922512 1.0786460025130806 0.8245590732171648 1.5794518998506037 0.12623929552501045 1.3487262190229805 0.8593807636108319 1.0353580485675642)
 (0.09620954840310136 0.2804712867454797 0.123724119342149 0.52911010973601 1.5224929924641024 0.8524251216796799 1.8222381897275512 1.552469980563295 0.8940626253184287 1.0586848393064772 1.6965821150677673 0.7910429914937751 1.9505076498899356 0.5905097358370057)
 (0.2639060808325666 0.49978925408657093 1.192260070853128 1.4923023878844541 0.289090244782056 0.1647353020903306 1.6927125137451902 1.0342929108237313 0.19612758771072425 1.0985323955146942 1.7320296190405506 1.759078571441371 0.35936130957770485 1.5795187832869542)
 (0.03450708881106879 0.7973050693782402 1.0629107006243226 1.4433489587947204 1.2098261974253672 1.7885002277514528 0.2771462192491314 0.6364379161285996 1.9934745026469851 1.7748966984868102 0.009007189957618289 1.3243037461147207 0.8426818002157399 1.6014376654012894)
 (0.23938907956874345 1.7787458699807772 1.394560426564912 1.7569893710721034 1.866780486055618 0.36619094565242083 1.7933966185542856 1.8156535527231048 1.4373466236696235 1.5424595431882355 0.3745189039460364 0.47680007215150866 1.2013036868492544 0.7344138978316561)
 (1.4173812647089985 1.2574224201670228 0.6257513923976286 0.62369960239817 0.08246855566771583 1.4246124261604511 0.19079704780122708 1.2962943817318093 1.2058207500728257 0.4902328894561365 0.14808607266389484 1.5042454730819985 1.926031029999444 1.953007158992031)
 (1.3204336131819223 0.32033194278113486 0.19270303654311594 1.05849793635318 1.0113339095992437 0.4116451392652747 0.5283521803783597 0.14982668173901215 1.571086371906326 1.8404904303050587 1.3716580472877702 1.265343660662269 1.3820929793172199 1.473657858594072)
 (0.2717766528565566 1.5202719957071993 1.9543063231274256 1.1070510402980782 0.5743919389254355 1.3735469077745552 1.311674713697102 1.7988950487775526 1.8723721907508168 0.7042503512004405 0.6380763270949845 1.9447103951760853 1.9864035844860706 0.0156445883775036)
 (0.30696087863146504 0.7955654160468439 1.3112866294152254 0.16557348184032872 0.7981610080846828 0.6937867138575258 0.18516973032376538 0.4307617703045774 0.9573976646464559 0.2668121667854657 0.4737037039189316 1.36038855502815 1.2170632864250415 0.7293218701355848)
 (0.6787301193655015 1.150401385192378 1.355253306939663 1.5549780818006997 0.9335019908407733 1.592776214840367 0.4235234086899091 1.518325235510043 1.9059441148056113 0.6674480359537616 1.5772933850811908 0.0865184683978586 0.1555770967922805 0.7191201047878315)
 (0.7931882802190386 1.3203759244159514 1.1866469170297065 1.5190031274950944 1.03924461251162 0.2258492191113599 1.737257690269974 0.4651467795856643 1.0650914831826228 0.847103166442799 1.089612290262641 0.8293502028322701 1.0384083242211566 0.5044686811785932)
)
(inputs estado))))))


(defvar *player5* (make-jugador 
	:nombre   '|player5|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player5))


(defun h-player6 (estado)
(+ 0.7778563039146691(prod-escalar '(0.7683214780884369 0.34848277491050483 1.0008979865320078 0.8987208599721419 1.06949075344009 0.43898374140147967 1.0478298868747724 1.7918354663271323 0.8469930430047303 1.3440038662923712 0.3678698741398405 0.031337819049993554 1.2924543289463024 0.5115889876893056)
(suma-vectores '(1.3572894648944613 0.3799165204279056 0.8349423985089113 1.137183688922194 0.7260797564634425 0.884204600698314 0.7278903860174817 1.862541349864702 0.24432249920754479 0.34718916265394695 0.29238557102711327 0.5834411539664497 0.9593809418167167 0.3467622901237881)(matriz-x-vector '((1.6111042086971359 0.7170222824408223 0.6498339712713599 1.0417019995850942 1.4190220396347433 1.4508277316206712 0.2481073321278482 1.9996460306784731 0.7376592301155458 0.18789141229075912 1.5593037874709417 1.8423491945780999 1.5614029961540805 1.4364106271329167)
 (1.9891244388704352 0.34386459444476647 0.17270275574550653 1.9128749213847316 0.5420996520112578 1.7681816682779365 0.5695847591115959 0.8428001774859863 0.44532886382695747 0.8019470094286885 1.5389015980632519 1.5087178567218689 1.3491022713150223 0.26525494793255344)
 (0.8991352535039072 1.2703981862410454 0.9974290709255635 0.48990730830626794 1.3803316289176055 0.9732238163957245 0.7177388262730562 0.5150379665156499 1.5133401788844956 0.8702814129001717 1.181000380017687 1.9599896741692007 1.0437417407572738 0.14333456607230466)
 (0.7450338415872235 0.4898889114726075 0.5384040375646104 0.5517434456878367 0.2927845129420663 1.3285460942506566 0.35866154670734574 1.9498490891153264 0.47940489051298774 0.8746101114796729 1.819865514494296 0.3852935313062873 0.4049664865810414 1.6537719283148167)
 (0.933873399471397 0.11511005317683876 1.9354170705551592 1.3768019153656483 0.22668500126489755 1.5764577800287187 0.56864434863911 1.0768045313575818 0.08629251622576795 1.07716711752077 0.8296496399533231 0.5859908695010865 0.5780089761160028 0.9285451990126676)
 (0.1270337018645682 1.1038215995867156 1.1282545108472972 0.3084723318384006 0.897956994019014 1.3091910157083528 0.4214825995524154 1.280215035083054 1.3421928228575835 0.7160262854330934 0.7426962642720494 1.3227317901933018 0.8516772732503861 0.20107934586718668)
 (0.7537135097586289 0.024588504722324656 0.43964679023591513 1.852034567107983 0.5753858886238901 1.794324476564536 1.940203007932134 0.10779920939524024 0.20035059457640392 1.7299590199502228 1.4360254015278118 1.9218958506901356 1.5466157858175038 1.6032381116314733)
 (1.6554101804758348 1.647931295690158 1.4783972861109553 1.3575985878673547 1.9301092629932783 0.7055123733714801 0.5294234485742257 0.4960481009972013 1.3271493136250019 1.1921090584171448 1.817262455525987 0.9631480637384551 1.274140102961818 1.377082342333822)
 (0.7374035738579972 1.004482623939886 0.4393545262943499 0.5953828718134666 1.631786879380649 1.6510440747795672 0.3864451575741821 1.6264132551137993 1.0064141586062665 1.0161469455612764 0.8100251180782272 1.032346584837959 0.1033437299562725 1.840553651598807)
 (0.4782782219996018 1.564885998919291 1.648965766475427 1.8883367039607843 0.9752466263337991 1.151590500507178 1.2396264807122166 1.0372185379139043 1.4458867136626459 0.6467288929670532 1.806325231539076 1.00721577187573 0.8504447483643578 0.25439977461767693)
 (0.1085730438075232 1.2660910229060307 1.169829954777773 0.2994205100604903 0.2175523531269754 1.4036870077793513 1.0781807424303287 1.8595807342414272 1.029080896818824 0.0454966059978239 1.5705728155437144 0.18883080418981213 1.8108457640051332 0.27560384042640185)
 (0.9366091544239254 0.9694179987944935 0.6514999518709395 1.8751451255181018 0.4512148896436903 0.8261517050776048 1.0832822866130019 1.2611324907107795 0.179089334024924 0.5885925397565186 0.6016019985001819 1.2499527004231181 0.2842353995731348 1.1782918898958765)
 (0.3850356842667939 1.1505383290455897 1.6623371838461094 1.806156396510547 1.8608405513166792 0.5095837441088384 1.8226015346358517 0.21244069288203415 0.6221587688491279 1.1964816201801098 1.7259715268342075 0.0506422809439564 1.5042485826983645 1.3608395183916133)
 (0.15299246432289948 1.7149339364041267 0.9762734438679852 0.4561382991883052 1.9201458595093148 1.742680355879363 0.9932646340806 0.07611008880255055 1.5933808770812923 1.4664016451888353 0.4321662718784365 1.7788310175036073 0.5867957126633314 1.7834219437562882)
)
(inputs estado))))))


(defvar *player6* (make-jugador 
	:nombre   '|player6|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player6))


(defun h-player7 (estado)
(+ 0.35145896129680954(prod-escalar '(1.3677326366433349 1.9687332627395806 0.24049884505409858 0.9875562330632242 0.21038519889489504 0.02041725409427797 1.912072294803758 0.04033348113028401 1.1590776908192364 1.7696148427729514 0.41819782322492616 1.658479225056927 0.6941607445367535 1.047639733761349)
(suma-vectores '(1.2974292218044488 0.3475644629713448 1.3832442716369975 1.215547472527757 0.4986597625902047 0.22150350419113685 0.6870622803214463 1.053593403366497 0.8844420018040704 1.972735798516045 0.231146376393341 0.0979054984995591 0.29387548601565583 1.5268038731548585)(matriz-x-vector '((0.8590183292008573 0.7653018062327623 1.366393877725748 1.6409132527534631 0.36442657232181186 1.1819912703671671 1.5492157148136423 0.15258576490434672 1.2814032140074414 1.5280680854799984 1.082961615620147 0.468333702679284 0.8908451370991466 1.1267302073607461)
 (0.945647670738551 0.13878069239049062 1.6804852907627108 0.6464872622636466 0.775220554433625 1.2564433351300062 0.05074241374658617 0.4736266835138907 1.1677535753743526 1.6123382179272319 1.7948804697394225 0.7080691795892946 1.428733348946873 1.9298886992384052)
 (1.7009326083972245 0.9811646562316909 1.5117589530791877 0.4051163093966519 1.9009760992330134 0.3467287279701865 0.47232973958503033 0.3188529500788111 0.6165664928933929 1.5022794249052513 1.2978774714967893 0.06882328732746479 1.7836977422325568 1.2315435345934187)
 (0.4118440022879284 1.096359489873661 1.2291553129163555 0.5054279846346734 0.5197336095599512 1.9976360701653775 0.45430826529700785 0.9030766559463048 1.6345201664121316 0.6790609607643794 1.1085547007828906 0.09185419912404025 1.6831006517992433 0.45486830721112725)
 (0.45352256017553216 0.7645753359708498 1.5076029860621991 0.8812861206113447 1.1547307014335346 0.31615511155636256 1.255234287614671 1.6771420079248693 0.17955999580018212 1.180028190879189 1.4433578025377223 1.9174403057746772 0.9934100713181544 1.3852024359990651)
 (1.9917259093368749 0.1806406892918344 1.7883289457470104 0.9772887550214215 1.258533812485943 1.0630510104943018 1.8750612566618476 1.5493481633236446 0.38346485526147944 0.20625401268948362 1.5976822854055728 1.8025202177439725 1.0538713889582803 1.5628856721627078)
 (0.3967804919152307 0.9688075772192024 1.4287211603914545 1.2697353950147128 1.444332905866997 1.937842821060789 0.3692280676728046 0.6921242457524706 0.049310106505318974 1.6721292732875042 0.7338679781163502 0.4081544356501532 0.8394064121207077 1.487521487765619)
 (0.7884573762252041 0.738800980848233 1.0543537225461168 1.8802602102456758 1.4329188424727126 1.57555634485856 0.15678656411717373 1.96119485680783 0.2938340788830862 1.6020186807516545 1.4300102991084167 0.5457585352935974 0.7036108858865466 0.4967636950257961)
 (1.3166129886239628 0.9441280520863546 1.5945962623762568 0.20818419676444622 0.7061708481684432 1.351115492843349 1.4573605642822074 0.5415239000665304 1.9902606431187297 0.6172141622202731 1.7257113922051652 0.7025105767354975 0.6116433571442308 1.9504451903003297)
 (0.4249042024827121 1.7905938372397903 1.4476924929289172 1.2213274249668256 0.7454276322028497 1.5964251889507528 0.2597086836318514 1.3968916113887337 1.0547824398273238 0.7147239730798323 1.0243587470541975 0.5584922450330356 1.2151185880112265 1.423027412357425)
 (0.13311147106063959 0.6243438948376006 0.14676988573463046 1.2324480942533265 0.4529403322971943 0.9100124789038373 0.34425211690782187 1.6627937951728085 0.7680571921560941 0.2815174529759441 0.5422186601968704 0.5073947891259034 0.5519176089411735 0.5549105422772556)
 (0.8939049396364607 0.22573329716396584 1.6601724200094177 1.4919076560785283 1.2306823988106748 0.47912159692321943 0.6620684234945013 0.2662122375587237 1.3448898954044957 1.183525298151571 0.7461186530427786 0.7700594559303438 1.8591450168154127 1.6833400493973631)
 (0.9054318266420265 0.7524441497960761 1.9534691173673377 1.8661598000986774 0.5153742547557061 0.2888370475080968 1.2030830960202044 1.0561919434853249 1.8916114419507326 1.812395420930386 0.509488311056356 1.3603663511226338 0.8418605621327351 0.011310196380946769)
 (0.1155432341418885 1.2970323541090305 0.7947370482938101 1.9456497680664702 1.4711468229104936 0.0674425273389212 0.10453484440687233 0.9941764473571566 1.0549830996847886 0.5362016133242833 1.3829175079338056 0.41001905896014623 1.7099010027004489 1.711268035535819)
)
(inputs estado))))))


(defvar *player7* (make-jugador 
	:nombre   '|player7|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player7))


(defun h-player8 (estado)
(+ 1.0782137042665743(prod-escalar '(1.648469766594732 1.8842703289839868 0.7866447011131239 1.2786168161306053 1.2731441864423405 1.821376140653557 0.34251715345000977 1.7074703100782764 1.5879892429069327 1.5782528026388956 0.27190846797622825 1.7934570385943673 0.6640592071030116 1.5193277335575914)
(suma-vectores '(1.2860510993764478 1.9130321221945836 1.346681243139261 1.1925525385745304 0.6307219455210247 0.10081026729531217 1.6775560680520294 1.1704554034247199 0.39500065938568296 0.02948697734960426 1.4289619538215268 1.63533412380324 0.02090560717665535 0.142354039181537)(matriz-x-vector '((1.8911402231687284 0.16254035554459745 1.5881101302782963 0.052583002118380406 0.9730447069245158 0.09415581699243414 0.513484518243762 1.517833106680626 0.6603332381876883 0.253856714907595 0.9580448482535322 1.0290873827107572 0.64819824404871 1.1884014433749)
 (1.839376164680343 1.5557113324049914 1.850443004793026 1.2580200377985733 1.967591202673663 1.7356640033454267 0.8093266028882751 0.005185000894470715 0.016932574369386222 0.6867537735889766 0.24043896187763547 1.9867308656662714 0.7084016954100312 1.1519410549476048)
 (0.5147343915537896 1.4807006016884434 1.7693046206337306 1.5932958865762157 1.8977174158046828 1.1320035535882935 1.2453207976864895 0.10618309240688806 0.2631756389340969 1.267499303852887 1.30401462782033 1.6148562798815835 0.0038355368140301493 1.2430309964044213)
 (0.5171995674558074 0.5342625991153929 1.549823334410161 0.35137510549368556 0.3057643413005313 1.0963626469904042 0.5882890327984933 1.586289651710704 1.8686996481096354 1.4860653335418639 0.22333642062395542 1.977007359761748 1.225539558052381 1.0182223053561972)
 (0.49639839271401187 0.31121513677547497 1.5211536544499613 0.1577642517240987 0.05009081197966725 1.5037619438546956 0.5109367878558055 1.9280053809217275 0.531508983157553 1.8537444669601748 0.29077239199420934 1.9022224897671094 1.5033924363502946 0.9496508608276177)
 (0.07058873750432704 1.5659569567172578 0.21604095403214085 1.7222750047161155 1.2248709787583718 1.818826418480622 0.8558735023670501 0.9064713628718022 0.7767999428908665 1.2881508801319275 1.8546543991486757 0.07646598221686207 1.4651350446108855 1.092398719735863)
 (0.5390065273554014 1.183694412715143 1.4838659454213277 1.2212204681451015 1.981878191788974 1.0923366762814364 0.5602484567252091 1.218829928331937 0.332493314289237 1.304234232204017 1.9370529473850755 1.6696047218030856 0.49482912456590555 1.9914522917155837)
 (1.1227665563364366 1.4357538865446933 1.7431893946962973 0.4402812913101892 0.54408856491535 0.27434300009053825 0.75929355858978 1.0113041003749512 0.09629425010227699 0.6944733279708966 1.9893652692232116 1.7920136498181305 1.673805580639835 0.9705739520747678)
 (0.18929956228034106 0.42237504920363866 0.47879932683282744 0.21457615851805767 0.5101458851802039 0.7405950870760074 0.1797079993337971 0.8939608404898123 1.9908500924493466 0.8539335216023278 0.1303556826581198 0.18651852618339126 1.979352253153494 1.942559603944613)
 (1.5947893040685028 0.5764167427411984 1.2795286612849301 1.1153788504533038 1.4527716715112657 0.07177167251316674 1.8014003946318828 1.1605308713275644 0.5172503720739863 1.7048460825364675 1.5324574226621523 1.7159584008503626 0.18706131096993328 0.6218222330596688)
 (1.2944737077711728 0.5298662106486178 0.14767217534749943 1.345844802899242 1.2410550012187886 0.3239673263021492 0.925062861772149 1.3239923661274313 0.10826467508391158 0.11257847676861066 0.8685627308009625 0.6002077523140579 1.2685295958611964 0.5275695117152317)
 (1.7095476524852231 1.2423088498620583 1.372675892138466 0.7409498655734224 1.547387528062348 1.8897600274114608 1.9321020237720345 0.5195957834855727 1.722030401140299 0.5155185882314754 0.8069406154811949 0.013564174130377138 0.09001611064936466 1.5918722080082022)
 (0.4467586879263179 0.8052548287896995 1.218840885424968 0.7876330894760761 1.4236183233770863 0.12172853649671755 0.12255182054751801 0.43322398174671384 1.7175440984445693 1.451084931322917 0.6337070796270463 1.2034148348269553 1.3819813222456208 1.6936598108918088)
 (0.3971474967932922 1.7966908504992658 1.8968477364945937 0.10329475585229098 1.9328793058069453 0.318055048637657 0.7204540859194819 0.6678744250265247 1.7758273516309655 1.8449699648458509 0.992534951383591 0.7457134298861894 0.08703253963788682 1.2550136291955347)
)
(inputs estado))))))


(defvar *player8* (make-jugador 
	:nombre   '|player8|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player8))


(defun h-player9 (estado)
(+ 0.2905419540231291(prod-escalar '(0.9968096976834411 1.0548069156009807 0.38706621048166 1.4472841819854227 1.713247922990088 1.839850764775767 1.9022225787889973 1.7482973320624646 1.6752626266722386 1.2070958916196783 0.35231421086645853 1.2079042535454971 0.9582863945637248 1.8634539908273406)
(suma-vectores '(0.5173785123564885 1.5290821745770053 0.9437995008642424 1.3504960492784794 0.7833117713752789 1.365419590137803 1.4887817490242328 1.307319180836589 1.539207698363349 1.7478777411770199 1.7462677125103567 1.7197276054570962 0.7211799591287318 0.9610364185509623)(matriz-x-vector '((0.20108012045438084 0.4099581146056077 0.4287862933066571 1.3230235410839908 0.5156363261465058 1.8686003552939443 0.9190546042284815 0.749650453983604 1.1107539812301332 1.9230806085707766 1.321904718608256 0.4428483297437096 1.533788812991343 0.7935396032996653)
 (0.15756499554945136 0.09131974971970269 1.5815799429321182 0.11826551717560263 1.1438813072210043 0.3139862510542524 0.8877573575808766 0.37820523800826455 1.47062611126468 1.5688301655026566 0.986361939064079 0.8537994627444261 1.2057482863972084 1.9806321778929286)
 (0.2442493047663825 0.8762423890668327 1.351694439814701 1.295795763904099 1.8793682413697335 0.7029116811813365 1.5611553258822177 1.2701229682836719 0.8598038155850389 0.5223611053804409 1.4955335420797826 1.9747364488873116 0.19301129002826767 1.5127870250453925)
 (0.5576652790705614 0.5310423544680218 0.6333667403465262 1.1338174329868183 1.6449760554741806 1.9085079903587365 1.5919538578761963 1.295460095953209 1.4899694091557933 0.5832346597318336 0.32613042615663645 1.8081158828027202 1.0143341940039432 0.8891640184742493)
 (0.5870462955404043 1.0463796093660513 1.9537916017047774 1.2941461681147368 0.5172363034667267 0.542906424532505 0.8255651223906373 1.65526393782181 0.8417556583158561 1.227071635476705 0.860831170268554 0.9362425061274249 1.9795349385286238 1.2802667746269945)
 (1.3400221784581492 0.667748790889461 1.2984130143836905 1.548670575077305 0.5799250098432447 1.8997600920649556 0.40485814999723213 1.7785447804323837 0.6347857900173619 1.995786881038792 0.7529415041966652 0.24277282665645505 1.3040593546772843 1.70216489251479)
 (0.9328026626108612 0.9318098907136718 1.3189806352828384 0.8305106899068602 1.1115935533120282 1.0685707962276612 0.4377866772531749 1.7644930313322997 1.1824994977631405 0.3180686700625026 0.8964465668497497 0.40244841541799614 0.6973420820830825 1.9914471747861404)
 (0.28757464255565424 1.6317936844993022 1.3525680107090483 1.4786266408796618 1.7688512371931582 1.4688690670583378 0.566314011890928 1.7520117520932108 0.7863625952652784 1.4655142620324446 1.9481156179509451 0.06799080826149195 1.4650139839679401 1.367177707402689)
 (1.4633440735687047 1.852400303262859 1.8568311929340482 0.725608312795158 1.7754216982872648 0.2951159858032706 1.9123631256737126 0.26317035069355077 1.834384344198401 1.7549262115155178 0.6264668338299204 1.5292060953505693 0.764672634564572 0.7507566834734272)
 (1.2165465555230044 1.6096727306321048 0.6277056404205141 1.2960395643810192 0.2930202825867352 0.7973705324079161 1.8452004984492045 1.7765615951742544 1.035408510194967 0.45212379766902044 1.3088219999035333 0.8067158303958262 0.35242804331334954 0.7196846793247589)
 (0.5205827869694899 0.4521755490792141 0.6814921834945118 1.4990090808774583 1.2073043189781225 1.2272472021217125 1.600987007952612 1.3049748909929593 0.6252210110500138 1.0181791751077358 0.3709854217852353 0.7834968144256733 1.3391594221416079 0.8725185767130652)
 (1.7458440705347547 1.2786742469794707 1.5951395716194918 1.380244830675163 0.8166720592815946 0.5175070356728213 0.8478977835670565 1.9353771252380678 1.2501990272782895 0.07170548903163154 1.2781869359995979 0.530280227462566 0.35569134152098125 1.9422480955560861)
 (1.2561977277497076 0.04852268969597051 1.2560461038729815 1.270228738255558 1.9268204878392008 1.6216284622101482 1.0510020924948495 0.22014587588292112 1.6802330673720107 0.47545935213670365 1.03323940805671 1.9742229420417208 0.7188390160689482 0.9034441781367064)
 (0.6111105696798855 0.7537195356484814 0.6829659252034359 0.444971097586049 0.003384819391650362 1.7818172488371502 1.5964644775197125 1.0567141181377218 1.3057677427621124 0.07710917046756549 0.29974104012420355 1.3775891503775781 0.6672991073178789 1.9752223143851726)
)
(inputs estado))))))


(defvar *player9* (make-jugador 
	:nombre   '|player9|
	:f-juego  #'f-j-nmx
	:f-eval   #'h-player9))

(partida 0 2 (list *player0*	*player1*))(partida 0 2 (list *player1*	*player0*))(partida 0 2 (list *player0*	*player2*))(partida 0 2 (list *player2*	*player0*))(partida 0 2 (list *player0*	*player3*))(partida 0 2 (list *player3*	*player0*))(partida 0 2 (list *player0*	*player4*))(partida 0 2 (list *player4*	*player0*))(partida 0 2 (list *player0*	*player5*))(partida 0 2 (list *player5*	*player0*))(partida 0 2 (list *player0*	*player6*))(partida 0 2 (list *player6*	*player0*))(partida 0 2 (list *player0*	*player7*))(partida 0 2 (list *player7*	*player0*))(partida 0 2 (list *player0*	*player8*))(partida 0 2 (list *player8*	*player0*))(partida 0 2 (list *player0*	*player9*))(partida 0 2 (list *player9*	*player0*))(partida 0 2 (list *player1*	*player2*))(partida 0 2 (list *player2*	*player1*))(partida 0 2 (list *player1*	*player3*))(partida 0 2 (list *player3*	*player1*))(partida 0 2 (list *player1*	*player4*))(partida 0 2 (list *player4*	*player1*))(partida 0 2 (list *player1*	*player5*))(partida 0 2 (list *player5*	*player1*))(partida 0 2 (list *player1*	*player6*))(partida 0 2 (list *player6*	*player1*))(partida 0 2 (list *player1*	*player7*))(partida 0 2 (list *player7*	*player1*))(partida 0 2 (list *player1*	*player8*))(partida 0 2 (list *player8*	*player1*))(partida 0 2 (list *player1*	*player9*))(partida 0 2 (list *player9*	*player1*))(partida 0 2 (list *player2*	*player3*))(partida 0 2 (list *player3*	*player2*))(partida 0 2 (list *player2*	*player4*))(partida 0 2 (list *player4*	*player2*))(partida 0 2 (list *player2*	*player5*))(partida 0 2 (list *player5*	*player2*))(partida 0 2 (list *player2*	*player6*))(partida 0 2 (list *player6*	*player2*))(partida 0 2 (list *player2*	*player7*))(partida 0 2 (list *player7*	*player2*))(partida 0 2 (list *player2*	*player8*))(partida 0 2 (list *player8*	*player2*))(partida 0 2 (list *player2*	*player9*))(partida 0 2 (list *player9*	*player2*))(partida 0 2 (list *player3*	*player4*))(partida 0 2 (list *player4*	*player3*))(partida 0 2 (list *player3*	*player5*))(partida 0 2 (list *player5*	*player3*))(partida 0 2 (list *player3*	*player6*))(partida 0 2 (list *player6*	*player3*))(partida 0 2 (list *player3*	*player7*))(partida 0 2 (list *player7*	*player3*))(partida 0 2 (list *player3*	*player8*))(partida 0 2 (list *player8*	*player3*))(partida 0 2 (list *player3*	*player9*))(partida 0 2 (list *player9*	*player3*))(partida 0 2 (list *player4*	*player5*))(partida 0 2 (list *player5*	*player4*))(partida 0 2 (list *player4*	*player6*))(partida 0 2 (list *player6*	*player4*))(partida 0 2 (list *player4*	*player7*))(partida 0 2 (list *player7*	*player4*))(partida 0 2 (list *player4*	*player8*))(partida 0 2 (list *player8*	*player4*))(partida 0 2 (list *player4*	*player9*))(partida 0 2 (list *player9*	*player4*))(partida 0 2 (list *player5*	*player6*))(partida 0 2 (list *player6*	*player5*))(partida 0 2 (list *player5*	*player7*))(partida 0 2 (list *player7*	*player5*))(partida 0 2 (list *player5*	*player8*))(partida 0 2 (list *player8*	*player5*))(partida 0 2 (list *player5*	*player9*))(partida 0 2 (list *player9*	*player5*))(partida 0 2 (list *player6*	*player7*))(partida 0 2 (list *player7*	*player6*))(partida 0 2 (list *player6*	*player8*))(partida 0 2 (list *player8*	*player6*))(partida 0 2 (list *player6*	*player9*))(partida 0 2 (list *player9*	*player6*))(partida 0 2 (list *player7*	*player8*))(partida 0 2 (list *player8*	*player7*))(partida 0 2 (list *player7*	*player9*))(partida 0 2 (list *player9*	*player7*))(partida 0 2 (list *player8*	*player9*))(partida 0 2 (list *player9*	*player8*))