# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0]`|`None`|`[ amounts \|-> SetAsFun({<<"ujuno", 2>>, <<"uosmo", 1>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("A")(1)`|`None`|`100000000000000000000`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"B", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"C", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>})`|`[ amounts \|-> SetAsFun({<<"ujuno", 2>>, <<"uosmo", 1>>}), sender \|-> "A", weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|
|`action.tag`|`Genesis`|`CreatePool`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value`|`0`|`[ id \|-> 1 ]`|
|`outcome.tag`|`Genesis`|`CreatePool`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("A")("ujuno")`|`8`|`6`|
|`bank("A")("uosmo")`|`8`|`7`|

</details>

</details>

## Step 2 to Step 3

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.id`|`None`|`1`|
|`action.value.share`|`None`|`300000000000000000000`|
|`action.tag`|`CreatePool`|`JoinPool`|
|`action.value.amounts`|`SetAsFun({<<"ujuno", 2>>, <<"uosmo", 1>>})`|`None`|
|`action.value.weights`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|`None`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.deltas`|`None`|`SetAsFun({<<"ujuno", 6>>, <<"uosmo", 3>>})`|
|`outcome.tag`|`CreatePool`|`UpdatePool`|
|`outcome.value.id`|`1`|`None`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("A")("ujuno")`|`6`|`0`|
|`bank("A")("uosmo")`|`7`|`4`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("A")(1)`|`100000000000000000000`|`400000000000000000000`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0].amounts("ujuno")`|`2`|`8`|
|`pools[0].amounts("uosmo")`|`1`|`4`|
|`pools[0].share`|`100000000000000000000`|`400000000000000000000`|

</details>

</details>

## Step 3 to Step 4

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[1]`|`None`|`[ amounts \|-> SetAsFun({<<"ujuno", 2>>, <<"uosmo", 4>>}), exit_fee \|-> 0, id \|-> 2, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.amounts`|`None`|`SetAsFun({<<"ujuno", 2>>, <<"uosmo", 4>>})`|
|`action.value.weights`|`None`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|
|`action.tag`|`JoinPool`|`CreatePool`|
|`action.value.sender`|`A`|`C`|
|`action.value.id`|`1`|`None`|
|`action.value.share`|`300000000000000000000`|`None`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("C")(2)`|`None`|`100000000000000000000`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.id`|`None`|`2`|
|`outcome.tag`|`UpdatePool`|`CreatePool`|
|`outcome.value.deltas`|`SetAsFun({<<"ujuno", 6>>, <<"uosmo", 3>>})`|`None`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("ujuno")`|`8`|`6`|
|`bank("C")("uosmo")`|`8`|`4`|

</details>

</details>

## Step 4 to Step 5

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.id`|`None`|`2`|
|`action.value.share`|`None`|`25000000000000000001`|
|`action.tag`|`CreatePool`|`JoinPool`|
|`action.value.sender`|`C`|`B`|
|`action.value.amounts`|`SetAsFun({<<"ujuno", 2>>, <<"uosmo", 4>>})`|`None`|
|`action.value.weights`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|`None`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("B")(2)`|`None`|`25000000000000000001`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.deltas`|`None`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 2>>})`|
|`outcome.tag`|`CreatePool`|`UpdatePool`|
|`outcome.value.id`|`2`|`None`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("B")("ujuno")`|`8`|`7`|
|`bank("B")("uosmo")`|`8`|`6`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[1].amounts("ujuno")`|`2`|`3`|
|`pools[1].amounts("uosmo")`|`4`|`6`|
|`pools[1].share`|`100000000000000000000`|`125000000000000000001`|

</details>

</details>

