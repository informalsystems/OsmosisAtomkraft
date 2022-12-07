# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0]`|`None`|`[ amounts \|-> SetAsFun({<<"ujuno", 100000000000000000000>>, <<"uosmo", 100000000000000000002>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("B")(1)`|`None`|`100000000000000000000`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000008>>, <<"uosmo", 100000000000000000008>>})>>, <<"B", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000008>>, <<"uosmo", 100000000000000000008>>})>>, <<"C", SetAsFun({<<"uatom", 100000000000000000008>>, <<"ujuno", 100000000000000000008>>, <<"uosmo", 100000000000000000008>>})>>})`|`[ amounts \|-> SetAsFun({<<"ujuno", 100000000000000000000>>, <<"uosmo", 100000000000000000002>>}), sender \|-> "B", weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|
|`action.tag`|`Genesis`|`CreatePool`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("B")("ujuno")`|`100000000000000000008`|`8`|
|`bank("B")("uosmo")`|`100000000000000000008`|`6`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value`|`0`|`[ id \|-> 1 ]`|
|`outcome.tag`|`Genesis`|`CreatePool`|

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
|`action.value.sender`|`B`|`A`|
|`action.value.amounts`|`SetAsFun({<<"ujuno", 100000000000000000000>>, <<"uosmo", 100000000000000000002>>})`|`None`|
|`action.value.weights`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|`None`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("A")(1)`|`None`|`1`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.deltas`|`None`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 2>>})`|
|`outcome.tag`|`CreatePool`|`UpdatePool`|
|`outcome.value.id`|`1`|`None`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("A")("ujuno")`|`100000000000000000008`|`100000000000000000007`|
|`bank("A")("uosmo")`|`100000000000000000008`|`100000000000000000006`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0].amounts("ujuno")`|`100000000000000000000`|`100000000000000000001`|
|`pools[0].amounts("uosmo")`|`100000000000000000002`|`100000000000000000004`|
|`pools[0].share`|`100000000000000000000`|`100000000000000000001`|

</details>

</details>

## Step 3 to Step 4

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[1]`|`None`|`[ amounts \|-> SetAsFun({<<"ujuno", 100000000000000000001>>, <<"uosmo", 100000000000000000003>>}), exit_fee \|-> 0, id \|-> 2, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.amounts`|`None`|`SetAsFun({<<"ujuno", 100000000000000000001>>, <<"uosmo", 100000000000000000003>>})`|
|`action.value.weights`|`None`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|
|`action.tag`|`JoinPool`|`CreatePool`|
|`action.value.sender`|`A`|`C`|
|`action.value.id`|`1`|`None`|
|`action.value.share`|`1`|`None`|

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
|`outcome.value.deltas`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 2>>})`|`None`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("ujuno")`|`100000000000000000008`|`7`|
|`bank("C")("uosmo")`|`100000000000000000008`|`5`|

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
|`action.value.share`|`None`|`4`|
|`action.tag`|`CreatePool`|`JoinPool`|
|`action.value.amounts`|`SetAsFun({<<"ujuno", 100000000000000000001>>, <<"uosmo", 100000000000000000003>>})`|`None`|
|`action.value.weights`|`SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>})`|`None`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.deltas`|`None`|`SetAsFun({<<"ujuno", 5>>, <<"uosmo", 5>>})`|
|`outcome.tag`|`CreatePool`|`UpdatePool`|
|`outcome.value.id`|`2`|`None`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("ujuno")`|`7`|`2`|
|`bank("C")("uosmo")`|`5`|`0`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("C")(2)`|`100000000000000000000`|`100000000000000000004`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[1].amounts("ujuno")`|`100000000000000000001`|`100000000000000000006`|
|`pools[1].amounts("uosmo")`|`100000000000000000003`|`100000000000000000008`|
|`pools[1].share`|`100000000000000000000`|`100000000000000000004`|

</details>

</details>

