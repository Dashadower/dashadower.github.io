---
layout: post
title: Coq Lemmas
usemathjax: true
---

# Basic Coq Lemmas

## Nat

### `plus_n_0`
```
forall n:nat, n = n + 0.
```

### `plus_0_n`
```
forall n:nat, 0 + n = n.
```

### `plus_n_Sm`
```
forall n m:nat, S (n + m) = n + S m.
```

### `plus_sn_m`
```
forall n m:nat, S n + m = S (n + m).
```

### `mult_n_0`
```
forall n:nat, 0 = n * 0.
```

### `mult_n_Sm`
```
forall n m:nat, n * m + n = n * S m.
```


