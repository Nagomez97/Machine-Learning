
(defun h_gen26player9 (estado)
(+ 0.4777888383740325
(prod-escalar '(0.02039641730851338 -0.29211306571303663 0.6545229467089271 0.7854820621267338 -0.03824240230792286 0.07714604454385232 -0.10896625656059866 -0.10953675054835643 0.55924591605122 -0.8896889321416213)
(suma-vectores '(0.3489093354525181 -0.8678613041059515 -0.28310850698460466 -0.18912396389357555 -0.11173985325134028 -0.6975583997164339 -0.6739607286138962 -0.8300878062557129 -0.22595726176053677 0.40902881872820385)
(matriz-x-vector '((0.09377988308205398 0.796722123037193 0.6431313293131473 -0.0430639026601658 0.1992075752854079 -0.12642984788671474 -0.577147909717574 -0.3049699501298031 -0.4373295524816727 -0.4844913392377519 0.6381403887703792 0.8155891366203931 -0.11218536113749678 -0.9363162407206045)
 (-0.09413569048400205 -0.4750726478984557 0.5192195760418028 -0.35704018389459846 -0.6692929389027 0.738966460895039 0.3992492599382975 -0.9424152722730552 0.4476495385945778 0.7572578292283589 -0.9916386001862156 -0.6634865898190017 0.4062502498169529 0.47227430317588426)
 (0.8456603538857235 -0.2647466160210392 0.6885534887758058 -0.6431408093109872 -0.325076320857661 -0.8098168387189746 0.4754419832608747 0.35999513750540246 -0.4991880337643726 -0.22420385936117304 0.28154305471200103 -0.6346787060391146 0.9510336689589545 0.7075456762801431)
 (0.4596798954760919 -0.36830613063330486 0.3453416716691282 0.4298030247329656 -0.4818310061528501 -0.28105180259252993 0.9281786703308679 0.6069137343398414 -0.4058252405062308 -0.1540118752517261 -0.8934928371594941 0.91899634150743 -0.109931703847995 -0.62033663173875)
 (-0.783978296834215 -0.33788301714947666 -0.7223027911683266 0.29812919987730724 0.30586984670467543 -0.6246615069889256 -0.7878436144345318 0.1545585456716383 -0.7937365691497704 0.8216493904317221 0.010038767040110086 -0.5300712613172691 -0.8031831234225084 -0.6111000293703643)
 (-0.7341455150200478 0.4680281313928214 -0.33140100808318906 0.7440567437845076 -0.9530029872736585 0.4014093145578417 0.2630529523662113 -0.17486321756819367 0.40738980066792574 0.612934932297299 0.12232542220445919 0.22920744834373052 -0.34483053212709347 0.6177558282125866)
 (0.8088356693026935 -0.3300937584718717 0.8093197816902058 0.9077519372397063 -0.45403242710418046 0.525002089663005 -0.9749393622927587 0.11308284362366483 -0.8996209409288496 -0.7420076226400991 0.7557025552048484 -0.8663337393678812 0.3345586175724313 0.3968968543134166)
 (-0.8289082815835283 -0.03822202862271906 0.1392599410939146 -0.07704829047169626 0.794275066261106 -0.7014203918423758 -0.661490526495288 0.5039210673378587 -0.10912354906151278 0.7127026204233124 -0.24657407885531368 -0.3815152803179336 0.6474133896287928 -0.748447442542802)
 (0.23081615616984452 0.13949431221242325 -0.5542726218249496 0.45957015264825163 -0.0642184862552031 0.4876523931742909 -0.8494887112440688 0.601461793954261 0.6466708449915377 -0.047219183298713 0.7801768710769514 -0.04122761314433143 -0.3468097095021978 -0.5683165237277814)
 (0.7713518638736685 0.27177974741980004 0.7624246632712914 0.7800807222492481 0.3761913123408034 0.4739156824457056 -0.8303762341354486 -0.7475698088555327 -0.4332924212071194 -0.7134474346157769 0.07108149209312531 -0.5885674541672636 -0.39407046849464367 0.9163865011993821)
)
(inputs estado))))))


(defvar *gen26player9* (make-jugador 
	:nombre   '|gen26player9|
	:f-juego  #'f-j-nmx
	:f-eval   #'h_gen26player9))

