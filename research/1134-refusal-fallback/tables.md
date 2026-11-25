| set | record | w | adaptive (route) | fallback fired? | discarded attempt | fallback | sig alone | fallback ÷ sig | bases agree |
|---|---|---:|---|---|---|---|---|---:|---|
| development | `sd-ellipsoid-m2@p31` | 1 | stopped: TooManyColumns (Shipping(DegreeSpread)) | **yes** | 894 ms, TooManyColumns | 1,417 ms | 516 ms | 2.75 | yes |
| development | `sd-ellipsoid-m2@p31` | 8 | stopped: TooManyColumns (Shipping(DegreeSpread)) | **yes** | 524 ms, TooManyColumns | 1,045 ms | 517 ms | 2.02 | yes |
| development | `sd-ellipsoid-m2@p64` | 1 | stopped: TooManyColumns (Shipping(DegreeSpread)) | **yes** | 905 ms, TooManyColumns | 1,421 ms | 523 ms | 2.71 | yes |
| development | `sd-ellipsoid-m2@p64` | 8 | stopped: TooManyColumns (Shipping(DegreeSpread)) | **yes** | 542 ms, TooManyColumns | 1,066 ms | 524 ms | 2.03 | yes |
| development | `gen-chandrasekhar-h-13@p31` | 1 | 21,734 ms (Signature) | no | – | 21,842 ms | 21,852 ms | 1.00 | yes |
| development | `gen-chandrasekhar-h-13@p31` | 8 | stopped: TooManyNonzeros (Shipping(Fallback(TooManyLiveBytes { bytes: 512108533, limit: 512000000 }))) | no | – | stopped: TooManyNonzeros | stopped: Budget(TooManyLiveBytes | – | – |
| development | `gen-chandrasekhar-h-13@p64` | 1 | 22,898 ms (Signature) | no | – | 22,872 ms | 22,819 ms | 1.00 | yes |
| development | `gen-chandrasekhar-h-13@p64` | 8 | stopped: TooManyNonzeros (Shipping(Fallback(TooManyLiveBytes { bytes: 512108533, limit: 512000000 }))) | no | – | stopped: TooManyNonzeros | stopped: Budget(TooManyLiveBytes | – | – |
| development | `zb-col-grid-5x5@p31` | 1 | 590 ms (Signature) | no | – | 585 ms | 592 ms | 0.99 | yes |
| development | `zb-col-grid-5x5@p31` | 8 | 538 ms (Signature) | no | – | 548 ms | 548 ms | 1.00 | yes |
| development | `zb-col-grid-5x5@p64` | 1 | 576 ms (Signature) | no | – | 591 ms | 589 ms | 1.00 | yes |
| development | `zb-col-grid-5x5@p64` | 8 | 542 ms (Signature) | no | – | 547 ms | 553 ms | 0.99 | yes |
| out-of-sample | `oos-reimer-5@p31` | 1 | 5 ms (Shipping(Small)) | no | – | 4 ms | 9 ms | 0.49 | yes |
| out-of-sample | `oos-reimer-5@p31` | 8 | 5 ms (Shipping(Small)) | no | – | 5 ms | 12 ms | 0.38 | yes |
| out-of-sample | `oos-reimer-7@p31` | 1 | 1,622 ms (Shipping(DegreeSpread)) | no | – | 1,613 ms | stopped: Budget(TooManyLiveBytes | – | yes |
| out-of-sample | `oos-reimer-7@p31` | 8 | 471 ms (Shipping(DegreeSpread)) | no | – | 465 ms | stopped: Budget(TooManyLiveBytes | – | yes |
| out-of-sample | `oos-cyclic-8@p31` | 1 | 2,887 ms (Shipping(DegreeSpread)) | no | – | 2,895 ms | 2,623 ms | 1.10 | yes |
| out-of-sample | `oos-cyclic-8@p31` | 8 | 781 ms (Shipping(DegreeSpread)) | no | – | 780 ms | 2,223 ms | 0.35 | yes |
| out-of-sample | `oos-katsura-11@p31` | 1 | 431 ms (Signature) | no | – | 427 ms | 434 ms | 0.98 | yes |
| out-of-sample | `oos-katsura-11@p31` | 8 | 143 ms (Signature) | no | – | 144 ms | 144 ms | 1.00 | yes |
| out-of-sample | `oos-eco-11@p31` | 1 | 202 ms (Signature) | no | – | 202 ms | 206 ms | 0.98 | yes |
| out-of-sample | `oos-eco-11@p31` | 8 | 144 ms (Signature) | no | – | 145 ms | 145 ms | 1.00 | yes |
| out-of-sample | `oos-noon-8@p31` | 1 | 125 ms (Signature) | no | – | 126 ms | 124 ms | 1.02 | yes |
| out-of-sample | `oos-noon-8@p31` | 8 | 125 ms (Signature) | no | – | 128 ms | 126 ms | 1.01 | yes |
| out-of-sample | `oos-col-grid-4x4@p31` | 1 | 3 ms (Signature) | no | – | 3 ms | 3 ms | 1.00 | yes |
| out-of-sample | `oos-col-grid-4x4@p31` | 8 | 5 ms (Signature) | no | – | 5 ms | 5 ms | 1.02 | yes |
| out-of-sample | `oos-col-gnm-16-24-s1@p31` | 1 | 18 ms (Signature) | no | – | 18 ms | 18 ms | 1.00 | yes |
| out-of-sample | `oos-col-gnm-16-24-s1@p31` | 8 | 21 ms (Signature) | no | – | 21 ms | 21 ms | 1.02 | yes |
| out-of-sample | `oos-pd-6-8-d2d4-s1@p31` | 1 | 14 ms (Shipping(DegreeSpread)) | no | – | 14 ms | 8 ms | 1.74 | yes |
| out-of-sample | `oos-pd-6-8-d2d4-s1@p31` | 8 | 10 ms (Shipping(DegreeSpread)) | no | – | 10 ms | 5 ms | 2.06 | yes |
| out-of-sample | `oos-pd-7-7-d2d4-s1@p31` | 1 | 514 ms (Shipping(DegreeSpread)) | no | – | 512 ms | 165 ms | 3.10 | yes |
| out-of-sample | `oos-pd-7-7-d2d4-s1@p31` | 8 | 150 ms (Shipping(DegreeSpread)) | no | – | 150 ms | 56 ms | 2.68 | yes |
| out-of-sample | `oos-pd-5-5-d2d5-s1@p31` | 1 | 5 ms (Shipping(Small)) | no | – | 5 ms | 2 ms | 2.58 | yes |
| out-of-sample | `oos-pd-5-5-d2d5-s1@p31` | 8 | 7 ms (Shipping(Small)) | no | – | 6 ms | 2 ms | 2.59 | yes |
| out-of-sample | `oos-pd-6-6-d3d5-s1@p31` | 1 | 1,880 ms (Shipping(DegreeSpread)) | no | – | 1,878 ms | 726 ms | 2.59 | yes |
| out-of-sample | `oos-pd-6-6-d3d5-s1@p31` | 8 | 482 ms (Shipping(DegreeSpread)) | no | – | 481 ms | 206 ms | 2.34 | yes |
| out-of-sample | `oos-det-2x5-quad-s1@p31` | 1 | 2 ms (Shipping(Small)) | no | – | 1 ms | 1 ms | 1.29 | yes |
| out-of-sample | `oos-det-2x5-quad-s1@p31` | 8 | 1 ms (Shipping(Small)) | no | – | 1 ms | 2 ms | 0.58 | yes |
| out-of-sample | `oos-det-2x6-quad-s1@p31` | 1 | 12 ms (Shipping(Small)) | no | – | 12 ms | 8 ms | 1.39 | yes |
| out-of-sample | `oos-det-2x6-quad-s1@p31` | 8 | 8 ms (Shipping(Small)) | no | – | 8 ms | 5 ms | 1.42 | yes |

Out of sample: the rule fired in 0 cells and completed 0 that `adaptive` refused at the same worker count.

**Predeclared decision:** no out-of-sample evidence.
