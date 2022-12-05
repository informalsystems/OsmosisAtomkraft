# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 1>>, <<"uosmo", 3>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"B", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>, <<"C", SetAsFun({<<"uatom", 8>>, <<"ujuno", 8>>, <<"uosmo", 8>>})>>})`|`[ amounts \|-> SetAsFun({<<"uatom", 6>>, <<"ujuno", 1>>, <<"uosmo", 3>>}), sender \|-> "C", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|
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

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("C")(1)`|`None`|`100000000000000000000`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("uatom")`|`8`|`2`|
|`bank("C")("ujuno")`|`8`|`7`|
|`bank("C")("uosmo")`|`8`|`5`|

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
|`action.value.share`|`None`|`1`|
|`action.tag`|`CreatePool`|`JoinPool`|
|`action.value.amounts`|`SetAsFun({<<"uatom", 6>>, <<"ujuno", 1>>, <<"uosmo", 3>>})`|`None`|
|`action.value.weights`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>})`|`None`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.deltas`|`None`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>})`|
|`outcome.tag`|`CreatePool`|`UpdatePool`|
|`outcome.value.id`|`1`|`None`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("uatom")`|`2`|`1`|
|`bank("C")("ujuno")`|`7`|`6`|
|`bank("C")("uosmo")`|`5`|`4`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("C")(1)`|`100000000000000000000`|`100000000000000000001`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0].amounts("uatom")`|`6`|`7`|
|`pools[0].amounts("ujuno")`|`1`|`2`|
|`pools[0].amounts("uosmo")`|`3`|`4`|
|`pools[0].share`|`100000000000000000000`|`100000000000000000001`|

</details>

</details>

## Step 3 to Step 4

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.share`|`1`|`50000000000000000001`|
|`action.tag`|`JoinPool`|`ExitPool`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("uatom")`|`1`|`4`|
|`bank("C")("ujuno")`|`6`|`7`|
|`bank("C")("uosmo")`|`4`|`6`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("C")(1)`|`100000000000000000001`|`50000000000000000000`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.deltas("uatom")`|`1`|`-3`|
|`outcome.value.deltas("ujuno")`|`1`|`-1`|
|`outcome.value.deltas("uosmo")`|`1`|`-2`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0].amounts("uatom")`|`7`|`4`|
|`pools[0].amounts("ujuno")`|`2`|`1`|
|`pools[0].amounts("uosmo")`|`4`|`2`|
|`pools[0].share`|`100000000000000000001`|`50000000000000000000`|

</details>

</details>

