# Historique des versions

Numérotation : `MAJEUR.MINEUR.CORRECTIF`.

- **MAJEUR** : le format des pages générées ou le fonctionnement de base change.
- **MINEUR** : nouvelle fonctionnalité visible.
- **CORRECTIF** : correction sans nouveauté.
- **Build** : +1 à chaque version livrée (la 2.5.0 est le build 17, la 2.5.1 le build 18).

Les versions antérieures à la 2.5.0 sont regroupées par grandes étapes (toutes n'ont pas été conservées une à une).

## 2.5.1 — build 18
- Documentation de l'en-tête, import inutilisé retiré.

## 2.5.0 — build 17
- Deux cases : « fichier unique » et « fichier par plateforme » (cumulables).
- Numéro de version affiché dans l'interface, `--version`, balise `generator` dans les pages.

## 2.4 — pages par plateforme
- Génération d'une page par plateforme ; historique réuni entre les pages ; correctif d'affichage mobile.

## 2.3 — interface responsive
- Interface en deux colonnes sur grand écran, une colonne sur mobile.

## 2.2 — images WebP
- Conversion en WebP avec Pillow, ImageMagick/GraphicsMagick ou ffmpeg ; plafond de poids sans outil ; conversion des anciens PNG sans retéléchargement.

## 2.1 — panneaux et correctif des images
- Séparation « connexions » / « boutiques sans connexion ».
- Réutilisation des images corrigée (redimensionnement local, erreurs SteamGridDB signalées, note explicative).

## 2.0 — plus de base locale
- L'historique, les images et les listes manuelles sont conservés dans la page générée.
- Jaquettes SteamGridDB, images réduites en base64.
- Changement de format des pages (migration automatique depuis les anciennes pages, par titre).

## 1.6 — NixOS et environnements sans SSL
- Certificats SSL retrouvés automatiquement, `--diagnostic`, secours `curl` si Python n'a pas de SSL.

## 1.5 — Steam, Ubisoft, Prime
- Steam par clé API ; listes manuelles pour Ubisoft Connect et Prime Gaming.

## 1.4 — vérification des connexions
- Contrôle des sessions au démarrage.

## 1.3 — doublons
- Fusion des jeux présents sur plusieurs plateformes, tags, choix du site au clic.

## 1.2 — Epic Games
- Connexion et bibliothèque Epic Games.

## 1.1 — téléchargements et liens
- Fichier dans le dossier de téléchargements ; clic sur une jaquette = page du jeu.

## 1.0 — application locale
- Interface dans le navigateur, connexion à GOG, génération en un clic.

## 0.2 / 0.1 — scripts initiaux
- `gog_to_html.py` : page hors ligne des jaquettes GOG, puis cache des jaquettes et badge « Nouveau ».
