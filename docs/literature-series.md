# Literature series inputs

The optional `hj9` and `bp12` methods use published expansion coefficients. Neither method reads any critical-point benchmark. Both are finite asymptotic truncations: their floating-point outputs are **not certified physical digits**, and adding terms can worsen low-dimensional predictions.

## Hellmund–Janke (`hj9`, q=1,2)

Source: M. Hellmund and W. Janke, *High-temperature series expansions for the q-state Potts model on a hypercubic lattice and critical properties of percolation*, Physical Review E **74**, 051113 (2006), [Eq. (12), PDF page 6](https://arxiv.org/pdf/cond-mat/0607423), [DOI](https://doi.org/10.1103/PhysRevE.74.051113).

For the branching number $\sigma=2d-1$, the paper expands its high-temperature variable $u=(e^K-1)/(e^K-1+q)$:

$$u^{(9)}=\sigma^{-1}\sum_{j=0}^{8}a_j(q)\sigma^{-j},\qquad \hat p=\frac{qu^{(9)}}{1+(q-1)u^{(9)}}.$$

| j | a_j(q) |
|---|---|
| 0 | 1 |
| 1 | 0 |
| 2 | (8−3q)/2 |
| 3 | 3(8−3q)/2 |
| 4 | 3(68−31q+q²)/2 |
| 5 | (8664−3798q−11q²)/12 |
| 6 | (78768−36714q+405q²−50q³)/12 |
| 7 | (1476192−685680q−2760q²−551q³)/24 |
| 8 | (7446864−3524352q−11204q²−6588q³−9q⁴)/12 |

The earlier GP4 estimator is this same coefficient input truncated at j=4. The implementation accepts only q=1,2: a high-temperature susceptibility singularity is not a valid replacement for the first-order Potts coexistence threshold at q=3. All nine displayed terms are used for `hj9`; its order was not selected against the benchmark table.

The full truncation is particularly poor for q=1,d=3 (about 0.572), and useful primarily at higher dimensions. The source itself warns that small dimensions require care with truncation order.

## Butera–Pernici (`bp12`, q=2)

Source: P. Butera and M. Pernici, *High-temperature expansions of the higher susceptibilities for the Ising model in general dimension d*, Physical Review E **86**, 011139 (2012), [Eq. (12), PDF page 8](https://arxiv.org/pdf/1209.3592), [DOI](https://doi.org/10.1103/PhysRevE.86.011139).

The paper uses the letter q for coordination number. Here we write **z=2d** to keep it distinct from the Potts state count q=2. Let $T_{12}(z)=\sum_{j=0}^{12}b_jz^{-j}$ with:

| j | b_j |
|---|---|
| 0 | 1 |
| 1 | −1 |
| 2 | −4/3 |
| 3 | −13/3 |
| 4 | −979/45 |
| 5 | −2009/15 |
| 6 | −176749/189 |
| 7 | −6648736/945 |
| 8 | −765907148/14175 |
| 9 | −5446232381/14175 |
| 10 | −829271458256/467775 |
| 11 | +164976684314/22275 |
| 12 | +6495334834824112/638512875 |

The implementation evaluates $K_{\rm Ising}=1/[zT_{12}(z)]$ and $\hat p=1-e^{-2K_{\rm Ising}}$. This is accurate at high d but is not a low-dimensional solver: at d=3 it yields about 0.415. The paper describes the asymptotic character as presumed for this Ising series, not proved convergence. No rigorous remainder bound is supplied here.

The high-d q=2 benchmarks from the same paper are a comparison with another analysis of related series data, not fully independent evidence.

## Exact susceptibility coefficient dataset

[data/ising_susceptibility_ht20.csv](../data/ising_susceptibility_ht20.csv) contains the integer susceptibility coefficients c0 through c20 for d=2,…,11, evaluated from Butera–Pernici Table I (PDF pages 6–7). The variable is u=tanh(K_Ising). The corresponding general-d rational polynomials and source information are preserved in [ising_susceptibility_ht20_polynomials.json](../data/ising_susceptibility_ht20_polynomials.json). Their rational evaluation was exact. All d=1 coefficients after c0 equal 2; the d=2 coefficients through c12 agree with the square-lattice sequence; d=3 coefficients through c20 agree with the independently recovered 32-order Arisue series. This dataset is provided for extending series analyses; it is not a table of thresholds.
