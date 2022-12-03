# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 8>>, <<"ujuno", 3>>, <<"uosmo", 6>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`Genesis`|`CreatePool`|
|`action.value`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"B", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>, <<"C", SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 21>>})>>})`|`[ amounts \|-> SetAsFun({<<"uatom", 8>>, <<"ujuno", 3>>, <<"uosmo", 6>>}), sender \|-> "C", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("uatom")`|`21`|`13`|
|`bank("C")("ujuno")`|`21`|`18`|
|`bank("C")("uosmo")`|`21`|`15`|

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
|`lp_bank("C")(1)`|`None`|`100000000000000000000`|

</details>

</details>

## Step 2 to Step 3

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`CreatePool`|`ExitPool`|
|`action.value.amounts`|`SetAsFun({<<"uatom", 8>>, <<"ujuno", 3>>, <<"uosmo", 6>>})`|`None`|
|`action.value.weights`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>})`|`None`|
|`action.value.id`|`None`|`1`|
|`action.value.share`|`None`|`50000000000000000001`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("uatom")`|`13`|`17`|
|`bank("C")("ujuno")`|`18`|`20`|
|`bank("C")("uosmo")`|`15`|`18`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("C")(1)`|`100000000000000000000`|`50000000000000000000`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.tag`|`CreatePool`|`ExitPool`|
|`outcome.value.denom`|`1`|`None`|
|`outcome.value.amounts`|`None`|`SetAsFun({<<"uatom", 4>>, <<"ujuno", 2>>, <<"uosmo", 3>>})`|
|`outcome.value.real_share`|`None`|`50000000000000000000`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0].amounts("uatom")`|`8`|`4`|
|`pools[0].amounts("ujuno")`|`3`|`1`|
|`pools[0].amounts("uosmo")`|`6`|`3`|
|`pools[0].share`|`100000000000000000000`|`50000000000000000000`|

</details>

</details>

## Step 3 to Step 4

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`ExitPool`|`JoinPool`|
|`action.value.share`|`50000000000000000001`|`175000000000000000000`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("C")("uatom")`|`17`|`1`|
|`bank("C")("ujuno")`|`20`|`16`|
|`bank("C")("uosmo")`|`18`|`6`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("C")(1)`|`50000000000000000000`|`250000000000000000000`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.tag`|`ExitPool`|`JoinPool`|
|`outcome.value.amounts("uatom")`|`4`|`16`|
|`outcome.value.amounts("ujuno")`|`2`|`4`|
|`outcome.value.amounts("uosmo")`|`3`|`12`|
|`outcome.value.real_share`|`50000000000000000000`|`200000000000000000000`|

</details>
<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[0].amounts("uatom")`|`4`|`20`|
|`pools[0].amounts("ujuno")`|`1`|`5`|
|`pools[0].amounts("uosmo")`|`3`|`15`|
|`pools[0].share`|`50000000000000000000`|`250000000000000000000`|

</details>

</details>

## Step 4 to Step 5

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[1]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 16>>}), denom \|-> 2, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`JoinPool`|`CreatePool`|
|`action.value.sender`|`C`|`A`|
|`action.value.id`|`1`|`None`|
|`action.value.share`|`175000000000000000000`|`None`|
|`action.value.amounts`|`None`|`SetAsFun({<<"uatom", 21>>, <<"ujuno", 21>>, <<"uosmo", 16>>})`|
|`action.value.weights`|`None`|`SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>})`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("A")("uatom")`|`21`|`0`|
|`bank("A")("ujuno")`|`21`|`0`|
|`bank("A")("uosmo")`|`21`|`5`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome.tag`|`JoinPool`|`CreatePool`|
|`outcome.value.amounts`|`SetAsFun({<<"uatom", 16>>, <<"ujuno", 4>>, <<"uosmo", 12>>})`|`None`|
|`outcome.value.real_share`|`200000000000000000000`|`None`|
|`outcome.value.denom`|`None`|`2`|

</details>
<details open>

<summary><code>lp_bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`lp_bank("A")(2)`|`None`|`100000000000000000000`|

</details>

</details>

## Step 5 to Step 6

<details open>

<summary>Variables</summary>

<details open>

<summary><code>pools</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`pools[2]`|`None`|`[ amounts \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 4>>}), denom \|-> 3, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.value.amounts("uatom")`|`21`|`1`|
|`action.value.amounts("ujuno")`|`21`|`1`|
|`action.value.amounts("uosmo")`|`16`|`4`|
|`action.value.sender`|`A`|`B`|

</details>
<details open>

<summary><code>bank</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`bank("B")("uatom")`|`21`|`20`|
|`bank("B")("ujuno")`|`21`|`20`|
|`bank("B")("uosmo")`|`21`|`17`|

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

