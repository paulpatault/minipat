# Minipat

Générateur aléatoire de problème de filtrage

## Usage

```
$ git clone https://github.com/paulpatault/minipat.git
$ dune build
$ ./genpat.exe -npat 1 -tuple 2 -typ-args 2 -dmax 3 ...
```

### Options

- `-ntyp`     : nombre de fichiers générés (chacun a un type aléatoire différents)
- `-npat`     : nombre de patterns matching dans chaque fichier généré
- `-dmax`     : profondeur max des patterns matching
- `-lmax`     : nombre max de ligne pour le filtrage généré
- `-orpat`    : fabrique des or-patterns
- `-suppr`    : supprime des lignes
- `-shuffle`  : mélange les lignes
- `-gen`      : si on veut écrire dans les fichiers plutot que print seulement
- `-pwhen`    : float qui indique la proba d'apparition d'un `when` sur une linge
- `-seed`     : pour la génération pseudo random
- `-typ-args` : arité max des constructeurs des types générés
- `-gospel`   : génération d'un fichier gospel
- `-tuple`    : pattern sur un n-uplet

