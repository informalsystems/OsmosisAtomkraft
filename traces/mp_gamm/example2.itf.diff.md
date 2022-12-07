# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 3>>, <<"ujuno", 2>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]`|

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
|`action.value`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>, <<"B", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>, <<"C", SetAsFun({<<"uatom", 5>>, <<"ujuno", 5>>, <<"uosmo", 5>>})>>})`|`[ amounts \|-> SetAsFun({<<"uatom", 3>>, <<"ujuno", 2>>}), sender \|-> "A", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]`|
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
|`bank("A")("uatom")`|`5`|`2`|
|`bank("A")("ujuno")`|`5`|`3`|

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
|`action.value.share`|`None`|`100000000000000000001`|
|`action.tag`|`CreatePool`|`JoinPool`|
|`action.value.sender`|`A`|`C`|
|`action.value.amounts`|`SetAsFun({<<"uatom", 3>>, <<"ujuno", 2>>})`|`None`|
|`action.value.weights`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>})`|`None`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("C")(1)`|`None`|`100000000000000000001`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.deltas`|`None`|`SetAsFun({<<"uatom", 4>>, <<"ujuno", 3>>})`|
|`outcome.tag`|`CreatePool`|`UpdatePool`|
|`outcome.value.id`|`1`|`None`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("uatom")`|`5`|`1`|
|`bank("C")("ujuno")`|`5`|`2`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0].amounts("uatom")`|`3`|`7`|
|`pools[0].amounts("ujuno")`|`2`|`5`|
|`pools[0].share`|`100000000000000000000`|`200000000000000000001`|

</details>

</details>

## Step 3 to Step 4

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[1]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}), exit_fee \|-> 0, id \|-> 2, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.amounts`|`None`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>})`|
|`action.value.weights`|`None`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>})`|
|`action.tag`|`JoinPool`|`CreatePool`|
|`action.value.id`|`1`|`None`|
|`action.value.share`|`100000000000000000001`|`None`|

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
|`outcome.value.deltas`|`SetAsFun({<<"uatom", 4>>, <<"ujuno", 3>>})`|`None`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("uatom")`|`1`|`0`|
|`bank("C")("ujuno")`|`2`|`1`|

</details>

</details>

## Step 4 to Step 5

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[2]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}), exit_fee \|-> 0, id \|-> 3, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>}) ]`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("B")(3)`|`None`|`100000000000000000000`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.sender`|`C`|`B`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("B")("uatom")`|`5`|`4`|
|`bank("B")("ujuno")`|`5`|`4`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.id`|`2`|`3`|

</details>

</details>

