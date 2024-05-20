module list[Time]

open order[Time]

abstract sig Item_Condition {}

one sig Outside_List_Item extends Item_Condition {}

one sig List_Item extends Item_Condition {}

sig Item {
	condition: Item_Condition one -> Time,
	next: Item lone -> Time,
	prev: Item lone -> Time
}

one sig List {
	items: Item -> Time
}

fun list_items[t : Time] : set Item { condition.t.List_Item }
fun unallocated_items[t : Time] : set Item { condition.t.Outside_List_Item }
fun all_next[i: Item, t:Time] : set Item { i.^(next.t) }
fun all_prev[i: Item, t:Time] : set Item { i.^(prev.t) }
fun all_reachable[i: Item, t:Time] : set Item { i.all_next[t] + i.all_prev[t] }
fun first_list_item[t : Time] : set Item { t.list_items - t.list_items.all_next[t] }
fun last_list_item[t : Time] : set Item { t.list_items - t.list_items.all_prev[t] }
fun item_with_neighbours[i : Item, t : Time] : set Item { i + i.next.t + i.prev.t }

pred list_valid[t : Time] {
	all i : t.list_items {
		some i.next.t implies i = i.next.t.prev.t
		some i.prev.t implies i = i.prev.t.next.t -- аналогично для предыдущих
	}
	all i : t.list_items | i not in i.all_reachable[t] -- нет циклов в элементах списка
	no (t.list_items & t.unallocated_items) -- элементы списка и свободные не пересекаются
	t.list_items = List.items.t -- все аллоцированные в списке 
	all i : t.list_items | i.all_reachable[t] + i = t.list_items -- все достижимые из каждого элемента - равны списку
	no t.first_list_item iff no t.last_list_item -- случай пустого списка
}

pred items_the_same_except[now : Time, changed_items : set Item] {
	let future = now.next {
		all it : Item - changed_items {
			it.condition.future = it.condition.now
			it.next.future = it.next.now
			it.prev.future = it.prev.now
			it in List.items.now iff it in List.items.future
		}
	}
}

pred empty[t : Time] {
	no it : Item | it.condition.t = List_Item
}

example: run {
	all t : Time {
		list_valid[t]
		#(t.list_items) >= 3 
	}
} for 6 but exactly 5 Item
