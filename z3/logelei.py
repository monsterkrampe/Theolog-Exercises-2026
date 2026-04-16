# z3 importieren
from z3 import *

# Atome deklarieren
A, B, C, D = Bools('A B C D')

# Beispiel aus der Vorlesung
logelei = Solver()          # Initialisierung eines Solver-Objekte
logelei.add(
    A == Not(B),            # Anna behauptet: "Barbara lügt!"
    B == Not(C),            # Barbara behauptet: "Chris lügt!"
    C == And(Not(A),Not(B)) # Chris behauptet: "Anna und Barbara lügen!"
)

print(logelei.check()) # prüft auf Erfüllbarkeit und gibt sat/unsat aus
print(logelei.model()) # gibt eine Wahrheitsbelegung aus (nach vorherigem Aufruf von check())

