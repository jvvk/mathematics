# Catalogue inputs for `src/fill.py`

These are Bouwkamp codes of perfect squared rectangles and squares, as published by David Moews
(http://xraysgi.ims.uconn.edu:8080/, retrieved 26 September 2026; the server no longer responds, and the pages are
not in the Internet Archive, so the copies used are kept here). The enumerations themselves are due to
C. J. Bouwkamp and A. J. W. Duijvestijn; see Moews's page for the references.

| File | Contents | Source file on Moews's page |
|---|---|---|
| `spsr16.txt` | the 12,679 simple perfect squared rectangles of orders 9 to 16 | `simple-perfect-rects-to-16.txt` |
| `bk21.txt` .. `bk26.txt` | simple perfect squared squares of orders 21 to 26 (1, 8, 12, 26, 160 and 441 codes) | `21-simple-sqsq.bouwkamp.txt` .. `26-simple-sqsq.bouwkamp.txt`, linked from `21-to-24-perfect-sq-sq.html` |

They are needed only to rerun the search that found the base-case tilings (`src/fill.py`). The proof does not
depend on them: every tiling it uses is in `../out/` and is checked by `../verify/audit.py` and in Lean.

SHA-256:

```
0f3bbd1c048233f81ecab06dbe316313b359bfa0608a490f24105542ef60ee19   bk21.txt
f6784a7c5d780dc6dea77f3c9b99c9c29c60ee70aced06fa39f00679a497a4fc   bk22.txt
a6dd2e84c813961abbc7158de08d220113cc69d6e2ba69f14a887d8e5d0d91e3   bk23.txt
efce7764d532d24cf06db8fa569224c729a90a399b33f71c147f41d7bb18efb3   bk24.txt
f280473813828dd727be77aef17e9571f891b55e09c9ce0ef3de507ea0ae0da6   bk25.txt
69393e99cfb5d2f0fadf27ba1a4c0559651bd41252b18c8a0b3635bcc121aba6   bk26.txt
99cf302fbdeae3bd74cd2bc264ae906b473bd3478cda6be43b742a5534906cd5   spsr16.txt
```
