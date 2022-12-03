# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 2>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`Genesis`|`CreatePool`|
|`action.value`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>, <<"B", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>, <<"C", SetAsFun({<<"uatom", 7>>, <<"ujuno", 7>>, <<"uosmo", 7>>})>>})`|`[ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 2>>}), sender \|-> "B", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("B")("uatom")`|`7`|`1`|
|`bank("B")("ujuno")`|`7`|`5`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.tag`|`Genesis`|`CreatePool`|
|`outcome.value`|`0`|`[ denom \|-> 1 ]`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("B")(1)`|`None`|`100000000000000000000`|

</details>

</details>

## Step 2 to Step 3

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[1]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 5>>}), denom \|-> 2, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.amounts("ujuno")`|`2`|`5`|
|`action.value.sender`|`B`|`C`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("uatom")`|`7`|`1`|
|`bank("C")("ujuno")`|`7`|`2`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.denom`|`1`|`2`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("C")(2)`|`None`|`100000000000000000000`|

</details>

</details>

## Step 3 to Step 4

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[2]`|`None`|`[ amounts \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}), denom \|-> 3, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.amounts("ujuno")`|`5`|`1`|
|`action.value.sender`|`C`|`B`|
|`action.value.amounts("uatom")`|`6`|`None`|
|`action.value.weights("uatom")`|`1`|`None`|
|`action.value.amounts("uosmo")`|`None`|`1`|
|`action.value.weights("uosmo")`|`None`|`1`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("B")("ujuno")`|`5`|`4`|
|`bank("B")("uosmo")`|`7`|`6`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.denom`|`2`|`3`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("B")(3)`|`None`|`100000000000000000000`|

</details>

</details>

## Step 4 to Step 5

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`CreatePool`|`ExitPool`|
|`action.value.amounts`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|`None`|
|`action.value.weights`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|`None`|
|`action.value.id`|`None`|`1`|
|`action.value.share`|`None`|`40000000000000000000`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("B")("uatom")`|`1`|`3`|
|`bank("B")("ujuno")`|`4`|`5`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("B")(1)`|`100000000000000000000`|`66666666666666666667`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.tag`|`CreatePool`|`ExitPool`|
|`outcome.value.denom`|`3`|`None`|
|`outcome.value.amounts`|`None`|`SetAsFun({<<"uatom", 2>>, <<"ujuno", 1>>})`|
|`outcome.value.real_share`|`None`|`33333333333333333333`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0].amounts("uatom")`|`6`|`4`|
|`pools[0].amounts("ujuno")`|`2`|`1`|
|`pools[0].share`|`100000000000000000000`|`66666666666666666667`|

</details>

</details>

## Step 5 to Step 6

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`ExitPool`|`JoinPool`|
|`action.value.id`|`1`|`3`|
|`action.value.share`|`40000000000000000000`|`200000000000000000001`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("B")("ujuno")`|`5`|`3`|
|`bank("B")("uosmo")`|`6`|`4`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("B")(3)`|`100000000000000000000`|`300000000000000000000`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.tag`|`ExitPool`|`JoinPool`|
|`outcome.value.amounts("ujuno")`|`1`|`2`|
|`outcome.value.real_share`|`33333333333333333333`|`200000000000000000000`|
|`outcome.value.amounts("uatom")`|`2`|`None`|
|`outcome.value.amounts("uosmo")`|`None`|`2`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[2].amounts("ujuno")`|`1`|`3`|
|`pools[2].amounts("uosmo")`|`1`|`3`|
|`pools[2].share`|`100000000000000000000`|`300000000000000000000`|

</details>

</details>

