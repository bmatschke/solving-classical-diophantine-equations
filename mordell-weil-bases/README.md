This folder contains Mordell-Weil bases for rational elliptic curves (mostly Mordell curves y^2 = x^3 + a) as sage object files.

- mwCremonaDB10000.sobj and mwCremonaDB100000.sobj are taken from [Cremona's database](https://github.com/JohnCremona/ecdata).
- mwMordell10000.sobj is taken from the [Gebel-Petho-Zimmer tables](http://tnt.math.metro-u.ac.jp/simath/MORDELL/), except that some errors were corrected, and missing curves filled in, and the resulting table was re-checked. Now it contains all bases for Mordell curves with |a| <= 10000.

All other files were computed from scratch, mostly using the script in mordell.sage, which is mostly based on various algorithms in sage, magma, and pari/GP. As it took a lot of effort, please cite them appropriately whenever you use them.

This folder is licensed under a Creative Commons BY-NC license.
Autors: Rafael von Kaenel, Benjamin Matschke.
