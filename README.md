## Pairing Heaps in Rocq

This repository contains a formalization of **pairing heaps** in **Rocq**, including:

✅ **Definitions**
- Pairing heaps over natural numbers.

✅ **Implementations**
- Core heap operations:
  - `meld`
  - `insert`
  - `delete_min`
  - `extract_min`
  - `find_min`

✅ **Proofs of correctness**
- Preservation of the **heap ordering invariant**.
- Preservation of the **multiset of elements** (permutation properties).
- Correctness of `find_min` in returning the minimum element.

---

## 📁 Repository structure

```
PairingHeap.v  - Main file containing:
                 • Type definitions (Heap, HeapNat)
                 • Implementation of heap operations
                 • Helper functions (e.g., elements, heap_ordered)
                 • Lemmas and proofs

README.md      - Project overview and usage instructions
```

---

## How to install and run

1️⃣ **Make sure you have Rocq installed**  
You can download it from the [official Rocq website](https://coq.inria.fr/download).

2️⃣ **Clone this repository**
```bash
git clone https://github.com/cosminvisan04/rocq-pairing-heaps
```

3️⃣ **Open `PairingHeap.v` in your Rocq environment**
- [RocqIDE](https://rocq-prover.org/install#windows-rocqide)
- [VSCode + Rocq extension](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq)

4️⃣ **Step through the proofs interactively**


## License

This project is licensed under the BSD 2-Clause License. See the [LICENSE](./LICENSE) file for details.
