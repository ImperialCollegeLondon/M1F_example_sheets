-- NOTE : I (KB) HAVE NOT TYPED UP THE SOLUTION SO THIS, SO THERE MAY BE MISTAKES

import data.nat.choose -- for choose = binomial coeffts

-- change RHS to what you think the sum is
theorem Q0403 : finset.sum (finset.range 51) (λ i, (-1 : ℤ) ^ i * choose 100 (2 * i)) = 0 := sorry