"""Download B. D. McKay's isotopy-class representatives for orders 4 to 7 into data/ and check their hashes.

Source: https://users.cecs.anu.edu.au/~bdm/data/latin.html (one Latin square per line, symbols from 0).
The files are not redistributed here; the SHA-256 values are those of the files used for the note.
"""
import hashlib
import urllib.request
from pathlib import Path

BASE = "https://users.cecs.anu.edu.au/~bdm/data/"
SHA256 = {4: '444a8baf6214bfaaf31789cf75efc679ca7b1e22901ea4f223c2d7b6f566b876', 5: 'b81db38692f4e161df9e5a805debb9c779a2fdfa02c1a6426f27aa237ec3201f', 6: 'b70cdad50b7269a97363334834f52e19c49711fdff5d9b6df7a0866ec32bc61d', 7: 'a7b19955e81ff9abeba0ba74fcc63bd13bd7ff0f77164038a595b8097faea979'}

data = Path(__file__).resolve().parent / "data"
data.mkdir(exist_ok=True)
for n, digest in SHA256.items():
    path = data / f"latin_is{n}.txt"
    if not path.exists():
        with urllib.request.urlopen(BASE + path.name, timeout=60) as r:
            path.write_bytes(r.read())
    got = hashlib.sha256(path.read_bytes()).hexdigest()
    assert got == digest, f"{path.name}: hash mismatch"
    print(f"{path.name}: ok")
