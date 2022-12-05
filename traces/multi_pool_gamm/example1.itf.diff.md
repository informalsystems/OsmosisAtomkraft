# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 2>>, <<"uosmo", 5>>}), exit_fee \|-> 0, id \|-> 1, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>, <<"B", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>, <<"C", SetAsFun({<<"uatom", 9>>, <<"ujuno", 9>>, <<"uosmo", 9>>})>>})`|`[ amounts \|-> SetAsFun({<<"uatom", 2>>, <<"uosmo", 5>>}), sender \|-> "B", weights \|-> SetAsFun({<<"uatom", 1>>, <<"uosmo", 1>>}) ]`|
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
|`lp_bank("B")(1)`|`None`|`100000000000000000000`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("B")("uatom")`|`9`|`7`|
|`bank("B")("uosmo")`|`9`|`4`|

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
|`action.value.share`|`None`|`160000000000000000001`|
|`action.tag`|`CreatePool`|`JoinPool`|
|`action.value.sender`|`B`|`A`|
|`action.value.amounts`|`SetAsFun({<<"uatom", 2>>, <<"uosmo", 5>>})`|`None`|
|`action.value.weights`|`SetAsFun({<<"uatom", 1>>, <<"uosmo", 1>>})`|`None`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("A")(1)`|`None`|`160000000000000000001`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.deltas`|`None`|`SetAsFun({<<"uatom", 4>>, <<"uosmo", 9>>})`|
|`outcome.tag`|`CreatePool`|`UpdatePool`|
|`outcome.value.id`|`1`|`None`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("A")("uatom")`|`9`|`5`|
|`bank("A")("uosmo")`|`9`|`0`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0].amounts("uatom")`|`2`|`6`|
|`pools[0].amounts("uosmo")`|`5`|`14`|
|`pools[0].share`|`100000000000000000000`|`260000000000000000001`|

</details>

</details>

## Step 3 to Step 4

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.share`|`160000000000000000001`|`1`|
|`action.value.sender`|`A`|`B`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("B")("uatom")`|`7`|`6`|
|`bank("B")("uosmo")`|`4`|`3`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("B")(1)`|`100000000000000000000`|`100000000000000000001`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.value.deltas("uatom")`|`4`|`1`|
|`outcome.value.deltas("uosmo")`|`9`|`1`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0].amounts("uatom")`|`6`|`7`|
|`pools[0].amounts("uosmo")`|`14`|`15`|
|`pools[0].share`|`260000000000000000001`|`260000000000000000002`|

</details>

</details>

