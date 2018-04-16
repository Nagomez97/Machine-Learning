import sys, os
import player
import tournament

os.system('clear')
sim_dir = './players/tournament'
load_dir = './players/load'

# Poner a False para no mostrar salidas de pantalla
verbose = True

# Se pone a True cuando se recibe la flag --load
load = False

if len(sys.argv) == 2:

	# Para simular un torneo entre jugadores ya almacenados
	if sys.argv[1] == '--simulate':
		players = []

		print('XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX')
		print('X                      Comienza el torneo                         X')
		print('XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX')

		if verbose:
			print('\n\n Simulando...\n\n')

		for filename in os.listdir(sim_dir):
			if filename.endswith(".pkl"):
				p = player.Player.load(sim_dir + '/' +filename)
				players.append(p)

		if len(players) > 0:
			t = tournament.Tournament(players)
			t.all_vs_all(verbose)	
			ranking = t.print_ranking(-1)
		else: 
			print("No players found.")
		
		sys.exit(0)

	# Para cargar jugadores del directorio load_dir
	elif sys.argv[1] == '--load':
		load = True
		loaded_players = []	
		for filename in os.listdir(load_dir):
			if filename.endswith(".pkl"):
				p = player.Player.load(sim_dir + '/' +filename)
				players.append(p)
		
		if len(loaded_players) <= 0:
			print("No players found.")
			sys.exit()			
	
# Para mas adelante elegir cuantas generaciones se crean en la ejecucion
	else:
		numGens = int(sys.argv[1])


else:
	numGens = 1

# Para elegir las generaciones que vamos a simular
if len(sys.argv) == 3:
	if sys.argv[1] == '--lisp':
		p = player.Player.load(sys.argv[2])
		f = open(p.name + '.cl', 'w+')
		f.write(str(p))
		f.close()
		print('generated', p.name + '.cl')
		sys.exit()
	

# Generacion original
gen = 0

os.system('clear')

if verbose:
	print('XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX')
	print('X                         Generación 0                            X')
	print('XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX')
else:
	print('\nGeneración 0...\n')

n = 'gen' + str(gen) + 'player'
players = [player.Player.random_player(n + str(i), 10, 14) for i in range(10)]

t = tournament.Tournament(players)
t.all_vs_all(verbose)

# print(top1.name, ':', score_top1['w'], 'ganadas	', score_top1['d'], 'empatadas	', score_top1['l'], 'perdidas')
# print(top2.name, ':', score_top2['w'], 'ganadas	', score_top2['d'], 'empatadas	', score_top2['l'], 'perdidas')

print('\n\n\n\nGen 0 Top 2:\n')

ranking = t.print_ranking(2)
top1, score_top1 = ranking[0]
top2, score_top2 = ranking[1]

top1.save()
top2.save()

for i in range(1, numGens):
	gen += 1

	if verbose:
		print('XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX')
		print('X                         Generación {}                            X'.format(gen))
		print('XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX')
	else:
		print('\n\nGeneración ' + str(gen) + '...\n')

	n = 'gen' + str(gen) + 'player'
	players = player.Player.new_generation(gen, top1, top2, 10, 10, 14)

	if load:
		t = tournament.Tournament(loaded_players)
	else:
		t = tournament.Tournament(players)

	t.all_vs_all(verbose)

	
	print('\n\n\n\nGen {} Top 2:'.format(gen))
	ranking = t.print_ranking(-1)
	top1, score_top1 = ranking[0]
	top2, score_top2 = ranking[1]
	top1.save()
	top2.save()
# top1.save()
# top2.save()