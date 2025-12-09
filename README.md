# ListLib - 列表操作库

本库提供列表相关的基础操作和性质证明，是算法验证中处理列表数据结构的核心工具库。

## 文件结构

```
ListLib/
├── Core.v          # 核心定义
├── Positional.v    # 位置相关操作
├── Inductive.v     # 归纳性质
└── Basics.v        # 基础引理和等价性证明
```

## 模块说明

### Core.v - 核心定义

定义列表的前缀、后缀和子列表的两种表示方法。

#### 主要定义

**归纳定义（基于列表拼接）：**
- `prefix_ind l1 l2`: `l1`是`l2`的前缀，即存在`l`使得`l2 = l1 ++ l`
- `suffix_ind l1 l2`: `l1`是`l2`的后缀，即存在`l`使得`l2 = l ++ l1`
- `sublist_ind l1 l2`: `l1`是`l2`的子列表，即存在`l3`、`l4`使得`l2 = l3 ++ l1 ++ l4`

**位置定义（基于索引操作）：**
- `prefix_pos l1 l2`: `l1`是`l2`的前缀，即存在`hi`使得`l1 = firstn hi l2`
- `suffix_pos l1 l2`: `l1`是`l2`的后缀，即存在`lo`使得`l1 = skipn lo l2`
- `sublist_pos l1 l2`: `l1`是`l2`的子列表，即存在`lo`、`hi`使得`l1 = skipn lo (firstn hi l2)`
- `sublist'_pos l1 l2`: 子列表的另一种位置定义，使用`firstn (skipn ...)`

### Positional.v - 位置相关操作

提供基于位置索引的列表操作函数及其性质。

#### 主要定义

- `to_sublist_pos lo hi l`: 提取列表`l`在区间`[lo, hi)`内的子列表

#### 核心引理

**长度相关：**
- `length_sublist`: 子列表长度计算
- `length_sublist'`: 带min的长度计算公式

**索引访问：**
- `nth_sublist`: 子列表的第`i`个元素等于原列表的第`i+lo`个元素
- `sublist_single`: 单元素子列表
- `sublist_one_ele`: 子列表追加单元素

**分割与组合：**
- `sublist_split`: 子列表的分割：`to_sublist_pos lo hi l = to_sublist_pos lo mid l ++ to_sublist_pos mid hi l`
- `sublist_split_app_l`: 左侧列表的子列表
- `sublist_split_app_r`: 右侧列表的子列表

**特殊情况：**
- `sublist_nil`: 空子列表
- `sublist_self`: 完整列表

**Forall2相关：**
- `Forall2_split`: `Forall2`在分割点的性质
- `combine_skipn`: `combine`与`skipn`的交换

### Inductive.v - 归纳性质

提供列表归纳性质和`Forall2`相关引理。

#### 主要引理

**列表构造：**
- `snoc_destruct`: 列表从后向前的归纳分解
- `app_cons`: 列表拼接与cons的转换

**Forall2操作：**
- `Forall2_congr`: `Forall2`的蕴含关系转换
- `Forall2_map1`: `Forall2`对第一个列表应用map
- `Forall2_map2`: `Forall2`对第二个列表应用map

### Basics.v - 基础引理

建立归纳定义与位置定义之间的等价关系，并提供各种转换引理。

#### 核心定理

**等价性定理：**
- `prefix_ind_iff_positional`: 前缀的两种定义等价
- `suffix_ind_iff_positional`: 后缀的两种定义等价
- `sublist_ind_iff_positional`: 子列表的两种定义等价

**标准化定义：**
```coq
Definition prefix {A: Type} := @prefix_ind A.
Definition suffix {A: Type} := @suffix_ind A.
Definition sublist {A: Type} := @sublist_ind A.
```

**记法：**
```coq
Notation "l1 'is_a_prefix_of' l2" := (prefix l1 l2)
Notation "l1 'is_a_suffix_of' l2" := (suffix l1 l2)
Notation "l1 'is_a_sublist_of' l2" := (sublist l1 l2)
```

**Forall2与nth的关系：**
- `Forall2_nth_iff`: `Forall2 P xs ys` 等价于长度相等且对应位置元素满足`P`

## 使用示例

```coq
Require Import ListLib.Basics.
Require Import ListLib.Positional.

(* 前缀判断 *)
Example prefix_example:
  [1; 2] is_a_prefix_of [1; 2; 3; 4].
Proof.
  exists [3; 4]. reflexivity.
Qed.

(* 子列表提取 *)
Example sublist_example:
  to_sublist_pos 1 3 [0; 1; 2; 3; 4] = [1; 2].
Proof.
  reflexivity.
Qed.

(* 子列表分割 *)
Example split_example:
  forall l, 
    to_sublist_pos 0 5 l = 
    to_sublist_pos 0 3 l ++ to_sublist_pos 3 5 l.
Proof.
  intros. apply sublist_split; lia.
Qed.
```

## 依赖关系

- **标准库**: `Coq.Lists.List`, `Coq.Arith.Arith`, `Lia`
- **内部依赖**: `Core` → `Positional` → `Inductive` → `Basics`

## 常用引理索引

### 列表前缀/后缀
- 判断：使用`prefix`/`suffix`定义
- 长度：`prefix_length`/`suffix_length`
- 等价：`prefix_ind_iff_positional`/`suffix_ind_iff_positional`

### 子列表操作
- 提取：`to_sublist_pos lo hi l`
- 访问：`nth_sublist`
- 长度：`length_sublist`
- 分割：`sublist_split`

### Forall2操作
- 逐点等价：`Forall2_nth_iff`
- 映射保持：`Forall2_map1`/`Forall2_map2`
- 分割：`Forall2_split`

---

*该库是CS2205图论算法验证项目的最短路的基础组件*

