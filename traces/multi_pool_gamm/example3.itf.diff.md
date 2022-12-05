# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 50000000000000000000>>, <<"ujuno", 1>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>, <<"B", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>, <<"C", SetAsFun({<<"uatom", 50000000000000000001>>, <<"ujuno", 50000000000000000001>>, <<"uosmo", 50000000000000000001>>})>>})`|`[ amounts \|-> SetAsFun({<<"uatom", 50000000000000000000>>, <<"ujuno", 1>>}), sender \|-> "A", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]`|
|`action.tag`|`Genesis`|`CreatePool`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("A")("uatom")`|`50000000000000000001`|`1`|
|`bank("A")("ujuno")`|`50000000000000000001`|`50000000000000000000`|

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
|`lp_bank("A")(1)`|`None`|`100000000000000000000`|

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
|`action.value.share`|`None`|`2`|
|`action.tag`|`CreatePool`|`JoinPool`|
|`action.value.sender`|`A`|`C`|
|`action.value.amounts`|`SetAsFun({<<"uatom", 50000000000000000000>>, <<"ujuno", 1>>})`|`None`|
|`action.value.weights`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>})`|`None`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("C")(1)`|`None`|`2`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.deltas`|`None`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>})`|
|`outcome.tag`|`CreatePool`|`UpdatePool`|
|`outcome.value.id`|`1`|`None`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("uatom")`|`50000000000000000001`|`50000000000000000000`|
|`bank("C")("ujuno")`|`50000000000000000001`|`50000000000000000000`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0].amounts("uatom")`|`50000000000000000000`|`50000000000000000001`|
|`pools[0].amounts("ujuno")`|`1`|`2`|
|`pools[0].share`|`100000000000000000000`|`100000000000000000002`|

</details>

</details>

## Step 3 to Step 4

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[1]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}), exit_fee \|-> 0, id \|-> 2, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.amounts`|`None`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>})`|
|`action.value.weights`|`None`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>})`|
|`action.tag`|`JoinPool`|`CreatePool`|
|`action.value.sender`|`C`|`A`|
|`action.value.id`|`1`|`None`|
|`action.value.share`|`2`|`None`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("A")(2)`|`None`|`100000000000000000000`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.id`|`None`|`2`|
|`outcome.tag`|`UpdatePool`|`CreatePool`|
|`outcome.value.deltas`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>})`|`None`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("A")("uatom")`|`1`|`0`|
|`bank("A")("ujuno")`|`50000000000000000000`|`49999999999999999999`|
|`bank("A")("uosmo")`|`50000000000000000001`|`50000000000000000000`|

</details>

</details>

