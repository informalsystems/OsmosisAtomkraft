# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 25000000000000000001>>, <<"ujuno", 3>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 2>>, <<"ujuno", 2>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`Genesis`|`CreatePool`|
|`action.value`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000004>>, <<"uosmo", 75000000000000000004>>})>>, <<"B", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000004>>, <<"uosmo", 75000000000000000004>>})>>, <<"C", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000004>>, <<"uosmo", 75000000000000000004>>})>>})`|`[ amounts \|-> SetAsFun({<<"uatom", 25000000000000000001>>, <<"ujuno", 3>>}), sender \|-> "B", weights \|-> SetAsFun({<<"uatom", 2>>, <<"ujuno", 2>>}) ]`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("B")("uatom")`|`75000000000000000004`|`50000000000000000003`|
|`bank("B")("ujuno")`|`75000000000000000004`|`75000000000000000001`|

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

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`CreatePool`|`JoinPool`|
|`action.value.sender`|`B`|`A`|
|`action.value.amounts`|`SetAsFun({<<"uatom", 25000000000000000001>>, <<"ujuno", 3>>})`|`None`|
|`action.value.weights`|`SetAsFun({<<"uatom", 2>>, <<"ujuno", 2>>})`|`None`|
|`action.value.id`|`None`|`1`|
|`action.value.share`|`None`|`250000000000000000000`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("A")("ujuno")`|`75000000000000000004`|`74999999999999999995`|
|`bank("A")("uatom")`|`75000000000000000004`|`1`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.tag`|`CreatePool`|`JoinPool`|
|`outcome.value.denom`|`1`|`None`|
|`outcome.value.amounts`|`None`|`SetAsFun({<<"uatom", 75000000000000000003>>, <<"ujuno", 9>>})`|
|`outcome.value.real_share`|`None`|`300000000000000000000`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0].amounts("uatom")`|`25000000000000000001`|`100000000000000000004`|
|`pools[0].amounts("ujuno")`|`3`|`12`|
|`pools[0].share`|`100000000000000000000`|`400000000000000000000`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("A")(1)`|`None`|`300000000000000000000`|

</details>

</details>

## Step 3 to Step 4

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[1]`|`None`|`[ amounts \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}), denom \|-> 2, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`JoinPool`|`CreatePool`|
|`action.value.sender`|`A`|`C`|
|`action.value.id`|`1`|`None`|
|`action.value.share`|`250000000000000000000`|`None`|
|`action.value.amounts`|`None`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|
|`action.value.weights`|`None`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("ujuno")`|`75000000000000000004`|`75000000000000000003`|
|`bank("C")("uosmo")`|`75000000000000000004`|`75000000000000000003`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.tag`|`JoinPool`|`CreatePool`|
|`outcome.value.amounts`|`SetAsFun({<<"uatom", 75000000000000000003>>, <<"ujuno", 9>>})`|`None`|
|`outcome.value.real_share`|`300000000000000000000`|`None`|
|`outcome.value.denom`|`None`|`2`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("C")(2)`|`None`|`100000000000000000000`|

</details>

</details>

## Step 4 to Step 5

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`CreatePool`|`JoinPool`|
|`action.value.amounts`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|`None`|
|`action.value.weights`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|`None`|
|`action.value.id`|`None`|`2`|
|`action.value.share`|`None`|`66666666666666666666`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("ujuno")`|`75000000000000000003`|`75000000000000000002`|
|`bank("C")("uosmo")`|`75000000000000000003`|`75000000000000000002`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("C")(2)`|`100000000000000000000`|`150000000000000000000`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.tag`|`CreatePool`|`JoinPool`|
|`outcome.value.denom`|`2`|`None`|
|`outcome.value.amounts`|`None`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|
|`outcome.value.real_share`|`None`|`50000000000000000000`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[1].amounts("ujuno")`|`1`|`2`|
|`pools[1].amounts("uosmo")`|`1`|`2`|
|`pools[1].share`|`100000000000000000000`|`150000000000000000000`|

</details>

</details>

## Step 5 to Step 6

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[2]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 50000000000000000003>>, <<"ujuno", 75000000000000000001>>, <<"uosmo", 3>>}), denom \|-> 3, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`JoinPool`|`CreatePool`|
|`action.value.sender`|`C`|`B`|
|`action.value.id`|`2`|`None`|
|`action.value.share`|`66666666666666666666`|`None`|
|`action.value.amounts`|`None`|`SetAsFun({<<"uatom", 50000000000000000003>>, <<"ujuno", 75000000000000000001>>, <<"uosmo", 3>>})`|
|`action.value.weights`|`None`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>})`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("B")("uosmo")`|`75000000000000000004`|`75000000000000000001`|
|`bank("B")("uatom")`|`50000000000000000003`|`0`|
|`bank("B")("ujuno")`|`75000000000000000001`|`0`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.tag`|`JoinPool`|`CreatePool`|
|`outcome.value.amounts`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|`None`|
|`outcome.value.real_share`|`50000000000000000000`|`None`|
|`outcome.value.denom`|`None`|`3`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("B")(3)`|`None`|`100000000000000000000`|

</details>

</details>

