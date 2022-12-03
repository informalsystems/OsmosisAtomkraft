# ITF Markdown

## Step 1

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "Genesis", value \|-> SetAsFun({<<"A", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000004>>, <<"uosmo", 75000000000000000004>>})>>, <<"B", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000004>>, <<"uosmo", 75000000000000000004>>})>>, <<"C", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000004>>, <<"uosmo", 75000000000000000004>>})>>}) ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000004>>, <<"uosmo", 75000000000000000004>>})>>, <<"B", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000004>>, <<"uosmo", 75000000000000000004>>})>>, <<"C", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000004>>, <<"uosmo", 75000000000000000004>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "Genesis", value \|-> 0 ]`|
|`pools`|`<<>>`|


</details>

## Step 2

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 25000000000000000001>>, <<"ujuno", 3>>}), sender \|-> "B", weights \|-> SetAsFun({<<"uatom", 2>>, <<"ujuno", 2>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000004>>, <<"uosmo", 75000000000000000004>>})>>, <<"B", SetAsFun({<<"uatom", 50000000000000000003>>, <<"ujuno", 75000000000000000001>>, <<"uosmo", 75000000000000000004>>})>>, <<"C", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000004>>, <<"uosmo", 75000000000000000004>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ denom \|-> 1 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 25000000000000000001>>, <<"ujuno", 3>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 2>>, <<"ujuno", 2>>}) ]>>`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 1, sender \|-> "A", share \|-> 250000000000000000000 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 1>>, <<"ujuno", 74999999999999999995>>, <<"uosmo", 75000000000000000004>>})>>, <<"B", SetAsFun({<<"uatom", 50000000000000000003>>, <<"ujuno", 75000000000000000001>>, <<"uosmo", 75000000000000000004>>})>>, <<"C", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000004>>, <<"uosmo", 75000000000000000004>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 300000000000000000000>>})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>})>>, <<"C", SetAsFun({})>>})`|
|`outcome`|`[ tag \|-> "JoinPool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 75000000000000000003>>, <<"ujuno", 9>>}), real_share \|-> 300000000000000000000 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 100000000000000000004>>, <<"ujuno", 12>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 400000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 2>>, <<"ujuno", 2>>}) ]>>`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}), sender \|-> "C", weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 1>>, <<"ujuno", 74999999999999999995>>, <<"uosmo", 75000000000000000004>>})>>, <<"B", SetAsFun({<<"uatom", 50000000000000000003>>, <<"ujuno", 75000000000000000001>>, <<"uosmo", 75000000000000000004>>})>>, <<"C", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000003>>, <<"uosmo", 75000000000000000003>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 300000000000000000000>>})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>})>>, <<"C", SetAsFun({<<2, 100000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ denom \|-> 2 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 100000000000000000004>>, <<"ujuno", 12>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 400000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 2>>, <<"ujuno", 2>>}) ], [ amounts \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}), denom \|-> 2, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 5

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "JoinPool", value \|-> [ id \|-> 2, sender \|-> "C", share \|-> 66666666666666666666 ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 1>>, <<"ujuno", 74999999999999999995>>, <<"uosmo", 75000000000000000004>>})>>, <<"B", SetAsFun({<<"uatom", 50000000000000000003>>, <<"ujuno", 75000000000000000001>>, <<"uosmo", 75000000000000000004>>})>>, <<"C", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000002>>, <<"uosmo", 75000000000000000002>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 300000000000000000000>>})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>})>>, <<"C", SetAsFun({<<2, 150000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "JoinPool", value \|-> [ amounts \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}), real_share \|-> 50000000000000000000 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 100000000000000000004>>, <<"ujuno", 12>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 400000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 2>>, <<"ujuno", 2>>}) ], [ amounts \|-> SetAsFun({<<"ujuno", 2>>, <<"uosmo", 2>>}), denom \|-> 2, exit_fee \|-> 0, share \|-> 150000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

## Step 6

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ tag \|-> "CreatePool", value \|-> [ amounts \|-> SetAsFun({<<"uatom", 50000000000000000003>>, <<"ujuno", 75000000000000000001>>, <<"uosmo", 3>>}), sender \|-> "B", weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ] ]`|
|`bank`|`SetAsFun({<<"A", SetAsFun({<<"uatom", 1>>, <<"ujuno", 74999999999999999995>>, <<"uosmo", 75000000000000000004>>})>>, <<"B", SetAsFun({<<"uatom", 0>>, <<"ujuno", 0>>, <<"uosmo", 75000000000000000001>>})>>, <<"C", SetAsFun({<<"uatom", 75000000000000000004>>, <<"ujuno", 75000000000000000002>>, <<"uosmo", 75000000000000000002>>})>>})`|
|`lp_bank`|`SetAsFun({<<"A", SetAsFun({<<1, 300000000000000000000>>})>>, <<"B", SetAsFun({<<1, 100000000000000000000>>, <<3, 100000000000000000000>>})>>, <<"C", SetAsFun({<<2, 150000000000000000000>>})>>})`|
|`outcome`|`[ tag \|-> "CreatePool", value \|-> [ denom \|-> 3 ] ]`|
|`pools`|`<<[ amounts \|-> SetAsFun({<<"uatom", 100000000000000000004>>, <<"ujuno", 12>>}), denom \|-> 1, exit_fee \|-> 0, share \|-> 400000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 2>>, <<"ujuno", 2>>}) ], [ amounts \|-> SetAsFun({<<"ujuno", 2>>, <<"uosmo", 2>>}), denom \|-> 2, exit_fee \|-> 0, share \|-> 150000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"ujuno", 1>>, <<"uosmo", 1>>}) ], [ amounts \|-> SetAsFun({<<"uatom", 50000000000000000003>>, <<"ujuno", 75000000000000000001>>, <<"uosmo", 3>>}), denom \|-> 3, exit_fee \|-> 0, share \|-> 100000000000000000000, swap_fee \|-> 0, weights \|-> SetAsFun({<<"uatom", 1>>, <<"ujuno", 1>>, <<"uosmo", 1>>}) ]>>`|


</details>

