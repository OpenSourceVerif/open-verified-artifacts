## Specs

- OS: Linux 7.1.3
- CPU: AMD Ryzen 9 5900XT
- Compiler: gcc 15.2.0

---

## Contains Cases

| Test                 | cnum.base       | cnum.size | value          |
| -------------------- | --------------- | --------- | -------------- |
| empty                | `U64_MAX`       | `U64_MAX` | 42             |
| non-overflow inside  | 1000            | 100       | 1050           |
| non-overflow outside | 1000            | 100       | 5000           |
| overflow high side   | `U64_MAX - 100` | 200       | `U64_MAX - 50` |
| overflow low side    | `U64_MAX - 100` | 200       | 50             |
| overflow outside     | `U64_MAX - 100` | 200       | 500            |
| singleton inside     | 42              | 0         | 42             |
| singleton outside    | 42              | 0         | 43             |
| full range           | 0               | `U64_MAX` | 123456         |

## Normalize Cases

| Test                    | cnum.base | cnum.size |
| ----------------------- | --------- | --------- |
| normal small range      | 1000      | 100       |
| full range normalized   | 0         | `U64_MAX` |
| full range nonzero base | 42        | `U64_MAX` |
| empty                   | `U64_MAX` | `U64_MAX` |
| signed max full range   | `S64_MAX` | `U64_MAX` |
| max base singleton      | `U64_MAX` | 0         |

## Smin/Smax Cases

| Test                     | cnum.base      | cnum.size |
| ------------------------ | -------------- | --------- |
| empty                    | `U64_MAX`      | `U64_MAX` |
| positive range           | 10             | 10        |
| negative range           | `(u64)-20`     | 10        |
| cross zero               | `(u64)-10`     | 20        |
| signed overflow boundary | `S64_MAX`      | 1         |
| signed overflow range    | `S64_MAX - 10` | 20        |
| unsigned overflow range  | `U64_MAX - 10` | 20        |
| full range               | 0              | `U64_MAX` |

## Results

### Contains

#### -O2

| Test                 | contains    | contains_new |
| -------------------- | ----------- | ------------ |
| empty                | 1.479 ns/op | 1.443 ns/op  |
| non-overflow inside  | 1.084 ns/op | 1.244 ns/op  |
| non-overflow outside | 1.079 ns/op | 1.247 ns/op  |
| overflow high side   | 1.472 ns/op | 1.249 ns/op  |
| overflow low side    | 1.468 ns/op | 1.247 ns/op  |
| overflow outside     | 1.467 ns/op | 1.249 ns/op  |
| singleton inside     | 1.041 ns/op | 1.243 ns/op  |
| singleton outside    | 1.054 ns/op | 1.249 ns/op  |
| full range           | 1.043 ns/op | 1.244 ns/op  |

#### -O0

| Test                    | contains     | contains_new |
| ----------------------- | ------------ | ------------ |
| normal small range      | 28.693 ns/op | 29.493 ns/op |
| full range normalized   | 29.944 ns/op | 29.629 ns/op |
| full range nonzero base | 29.983 ns/op | 29.890 ns/op |
| empty                   | 29.620 ns/op | 29.578 ns/op |
| signed max full range   | 29.882 ns/op | 29.584 ns/op |
| max base singleton      | 29.076 ns/op | 29.336 ns/op |

## Normalize

#### -O2

| Test                    | normalize   | normalize_new |
| ----------------------- | ----------- | ------------- |
| normal small range      | 1.255 ns/op | 1.217 ns/op   |
| full range normalized   | 1.019 ns/op | 1.217 ns/op   |
| full range nonzero base | 1.031 ns/op | 1.221 ns/op   |
| empty                   | 1.023 ns/op | 1.217 ns/op   |
| signed max full range   | 1.020 ns/op | 1.218 ns/op   |
| max base singleton      | 1.218 ns/op | 1.219 ns/op   |

#### -O0

| Test                    | normalize    | normalize_new |
| ----------------------- | ------------ | ------------- |
| normal small range      | 29.036 ns/op | 28.808 ns/op  |
| full range normalized   | 29.175 ns/op | 28.797 ns/op  |
| full range nonzero base | 29.161 ns/op | 28.892 ns/op  |
| empty                   | 28.873 ns/op | 28.975 ns/op  |
| signed max full range   | 29.252 ns/op | 28.517 ns/op  |
| max base singleton      | 28.965 ns/op | 28.586 ns/op  |

## Smin

#### -O2

| Test                     | smin        | smin_new    |
| ------------------------ | ----------- | ----------- |
| empty                    | 1.866 ns/op | 1.477 ns/op |
| positive range           | 1.870 ns/op | 1.248 ns/op |
| negative range           | 1.657 ns/op | 1.246 ns/op |
| cross zero               | 1.870 ns/op | 1.660 ns/op |
| signed overflow boundary | 1.463 ns/op | 1.049 ns/op |
| signed overflow range    | 1.519 ns/op | 1.050 ns/op |
| unsigned overflow range  | 1.883 ns/op | 1.669 ns/op |
| full range               | 1.555 ns/op | 1.049 ns/op |

#### -O0

| Test                     | smin          | smin_new      |
| ------------------------ | ------------- | ------------- |
| empty                    | 46.532 ns/op  | 45.927 ns/op  |
| positive range           | 61.699 ns/op  | 61.994 ns/op  |
| negative range           | 61.300 ns/op  | 61.085 ns/op  |
| cross zero               | 61.237 ns/op  | 61.725 ns/op  |
| signed overflow boundary | 106.577 ns/op | 105.276 ns/op |
| signed overflow range    | 105.212 ns/op | 104.999 ns/op |
| unsigned overflow range  | 61.947 ns/op  | 61.421 ns/op  |
| full range               | 105.264 ns/op | 105.165 ns/op |

## Smax

#### -O2

| Test                     | smax        | smax_new    |
| ------------------------ | ----------- | ----------- |
| empty                    | 1.462 ns/op | 1.456 ns/op |
| positive range           | 1.250 ns/op | 1.249 ns/op |
| negative range           | 1.259 ns/op | 1.297 ns/op |
| cross zero               | 1.471 ns/op | 1.475 ns/op |
| signed overflow boundary | 1.056 ns/op | 1.260 ns/op |
| signed overflow range    | 1.049 ns/op | 1.259 ns/op |
| unsigned overflow range  | 1.470 ns/op | 1.477 ns/op |
| full range               | 1.072 ns/op | 1.263 ns/op |

#### -O0

| Test                     | smax          | smax_new      |
| ------------------------ | ------------- | ------------- |
| empty                    | 46.591 ns/op  | 46.521 ns/op  |
| positive range           | 61.690 ns/op  | 61.406 ns/op  |
| negative range           | 61.589 ns/op  | 61.359 ns/op  |
| cross zero               | 61.904 ns/op  | 62.069 ns/op  |
| signed overflow boundary | 106.315 ns/op | 105.190 ns/op |
| signed overflow range    | 104.641 ns/op | 103.921 ns/op |
| unsigned overflow range  | 61.729 ns/op  | 61.808 ns/op  |
| full range               | 105.549 ns/op | 104.930 ns/op |
