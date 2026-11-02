# Bibliothèque de jeux hors ligne

Génère **une page web autonome** (un seul fichier HTML, utilisable hors ligne) avec les jaquettes de tes
jeux **GOG, Epic Games, Steam, Ubisoft Connect et Prime Gaming**, à partager facilement.

> Projet non officiel, sans lien avec GOG, Epic Games, Valve, Ubisoft, Amazon ni SteamGridDB.

## Fonctionnalités

- **Un fichier HTML unique**, jaquettes intégrées (WebP réduit, encodé en base64) : s'ouvre hors ligne dans n'importe quel navigateur, responsive.
- Recherche, filtre par plateforme, badge **« Nouveau »** (jeux ajoutés depuis la génération précédente).
- **Doublons fusionnés** : un jeu présent sur plusieurs plateformes n'a qu'une carte, avec un tag par plateforme ; un clic propose d'ouvrir la page du jeu sur le site de votre choix.
- **Fichier unique et/ou un fichier par plateforme**.
- Jaquettes verticales de [SteamGridDB](https://www.steamgriddb.com/) en option (sinon, celles des boutiques).
- **Aucune base de données** : l'historique, les images et les listes manuelles sont conservés dans la page générée, qui sert d'« ancien fichier » à la génération suivante. Seules les connexions (jetons) sont enregistrées.
- Interface locale (dans le navigateur), en deux colonnes sur grand écran, une seule colonne sur mobile.

## Prérequis

- Python 3 (testé avec Python 3.12), sans dépendance obligatoire.
- Recommandé : **Pillow** (`pip install --user pillow`) pour réduire les images en WebP. À défaut, ImageMagick ou ffmpeg sont utilisés ; sans aucun de ces outils, les images lourdes sont ignorées.
- Si ton Python n'a pas de support SSL, `curl` est utilisé automatiquement.

## Démarrage

```bash
python3 gog_library.py
```

L'interface s'ouvre dans le navigateur :

1. **Connexions** : connecte les plateformes (voir ci-dessous).
2. **Boutiques sans connexion** : renseigne la liste de tes jeux Ubisoft Connect / Prime Gaming.
3. **Ta bibliothèque** : choisis « Un fichier unique » et/ou « Un fichier par plateforme », la taille des images, puis **Générer**.

Les fichiers sont écrits dans ton dossier de téléchargements (`ma_bibliotheque_jeux.html`, `ma_bibliotheque_jeux_gog.html`, …).

## Connexion aux plateformes

| Plateforme | Méthode |
|---|---|
| GOG | Connexion sur gog.com, puis copier l'adresse de la page affichée et la coller dans l'application. |
| Epic Games | Connexion sur epicgames.com, puis copier le texte de la page (`authorizationCode`) et le coller. Le code expire vite et ne sert qu'une fois : ne le partage pas. |
| Steam | Clé API gratuite + profil dont « Détails des jeux » est public. |
| SteamGridDB (facultatif) | Clé API gratuite (Préférences > API). |
| Ubisoft Connect, Prime Gaming | Pas d'accès public : liste saisie à la main (`Titre \| lien \| image`, lien et image facultatifs). |

Ton mot de passe n'est jamais vu par l'application : la connexion se fait sur le site de la plateforme.

## Ligne de commande

```bash
python3 gog_library.py --auto                                      # page unique
python3 gog_library.py --auto --par-plateforme                     # page unique + une page par plateforme
python3 gog_library.py --auto --par-plateforme --sans-page-unique  # seulement une page par plateforme
python3 gog_library.py --auto --previous ANCIENNE.html --taille legere
```

| Option | Rôle |
|---|---|
| `--auto` | Génère sans interface (après une première connexion via l'interface). |
| `--par-plateforme` | Génère aussi une page par plateforme. |
| `--sans-page-unique` | Ne génère pas la page unique (avec `--par-plateforme`). |
| `--previous FICHIER` | Ancienne page à utiliser (nouveaux jeux, images déjà prêtes). |
| `--taille {legere,standard,haute}` | Taille des images. |
| `--refresh-images` | Retraite toutes les images. |
| `--out FICHIER` | Fichier de sortie. |
| `--diagnostic` | Teste le réseau, les certificats SSL et l'outil de conversion d'images. |
| `--nettoyer` | Supprime les fichiers d'une ancienne version (cache, historique). |
| `--install-shortcut` | Ajoute un lanceur au menu des applications. |
| `--version` | Affiche la version. |

## Nouveaux jeux et images : l'« ancien fichier »

À chaque génération, l'application relit la page précédente (celle du dossier de sortie, ou un fichier choisi
avec « Charger un ancien fichier… » / `--previous`). Elle en tire la liste des jeux déjà connus, pour afficher
le badge « Nouveau » pendant 30 jours, et les images déjà préparées, qui sont réutilisées sans rien retélécharger.
**Garde ta dernière page** : c'est elle qui contient l'historique.

## Confidentialité

- Les jetons de connexion sont dans `~/.config/gog-bibliotheque/` (lisibles par toi seul). « Se déconnecter » les supprime.
- L'application ne contacte que les plateformes concernées et SteamGridDB (si activé).
- Les pages générées contiennent la liste de tes jeux, mais aucun identifiant ni jeton.

## Limites

- Utilise les API non documentées de GOG et d'Epic Games (comme Heroic ou Legendary) : elles peuvent changer.
- Le programme contient les identifiants publics des clients GOG Galaxy et du lanceur Epic Games, utilisés par ces mêmes outils.
- Ubisoft Connect et Prime Gaming n'offrent pas d'accès public à la bibliothèque : d'où les listes manuelles.

## Numérotation

`MAJEUR.MINEUR.CORRECTIF` (+ numéro de build). Voir [CHANGELOG.md](CHANGELOG.md).

## Licence

Aucune licence n'est définie pour le moment : ajoute un fichier `LICENSE` de ton choix avant de publier le dépôt.
