#include <cstdlib>
#include <utility>
#include <type_traits>
#include <cstddef>

template<typename...Ts>
struct TypeList {};

template<typename C, typename R, typename...A>
constexpr size_t argc_of (R(C::*)(A...)) {
    return sizeof...(A);
}

template<typename P, typename F>
struct SeparationResult {
    using pass = P;
    using fail = F;
};

template<auto...methods>
struct OverloadSet {
    static constexpr size_t count = sizeof...(methods);
};

template<typename Pred, auto head, auto...methods, auto...p, auto...f>
auto SeparateOverloads(OverloadSet<head, methods...>, OverloadSet<p...>, OverloadSet<f...>) {
    if constexpr (!sizeof...(methods)) {
        if constexpr (Pred::check(head)) {
            return SeparationResult<OverloadSet<p..., head>, OverloadSet<f...>>{};
        } else {
            return SeparationResult<OverloadSet<p...>, OverloadSet<f..., head>>{};
        }
    } else if constexpr (Pred::check(head)) {
        return SeparateOverloads<Pred>(
            OverloadSet<methods...>{}, OverloadSet<p..., head>{}, OverloadSet<f...>{});
    } else {
        return SeparateOverloads<Pred>(
            OverloadSet<methods...>{}, OverloadSet<p...>{}, OverloadSet<f..., head>{});
    }
}

template<auto...l, auto...r, typename...Tail>
auto concat(OverloadSet<l...>, OverloadSet<r...>, Tail...) {
    if constexpr (!sizeof...(Tail)) {
        return OverloadSet<l..., r...>{};
    } else {
        return concat(OverloadSet<l..., r...>{}, Tail{}...);
    }
}


template<typename Pred, auto...methods>
auto FilterOverloads(OverloadSet<methods...>)
    -> decltype(concat(std::conditional_t<Pred::check(methods), OverloadSet<methods>, OverloadSet<>>{}...));


// resulting type has two typedefs
// pass: all methods passing predicate
// fail: all methods failing predicate
template<typename Pred, typename Set>
using separated_t = decltype(SeparateOverloads<Pred>(Set{}, OverloadSet<>{}, OverloadSet<>{}));

template<typename Pred, typename Set>
using filtered_t = decltype(FilterOverloads<Pred>(Set{}));

// emulate generic deserializable value
struct Arg {
    template<typename T>
    bool get(T& v) {
        v = {};
        return rand() & 1;
    }
    template<typename T>
    void set(T) {}
};

template<typename...Ms>
constexpr size_t max_argc(Ms...methods) {
    size_t res = 0;
    ((argc_of(methods) > res && (res = argc_of(methods))), ...);
    return res;
}

template<size_t...Is, typename Fn>
constexpr void const_for_each(std::index_sequence<Is...>, Fn f) {
    (f(std::integral_constant<size_t, Is>{}), ...);
}

template<size_t argc>
struct CanBeCalledWith {

    template<typename R, typename T, typename...Args>
    static constexpr size_t check(R(T::*)(Args...)) {
        return sizeof...(Args) == argc;
    }
};

template<size_t i, typename First, typename...Rest>
auto item_at_idx(TypeList<First, Rest...>) {
    if constexpr (!i) return First{};
    else return item_at_idx<i - 1>(TypeList<Rest...>{});
}

template<size_t pos, typename R, typename T, typename...Args>
auto arg_at_pos(R(T::*)(Args...)) -> decltype(item_at_idx<pos>(TypeList<Args...>{}));

template<size_t pos, typename T, typename C, typename R, typename...Args>
constexpr bool same_arg_at(R(C::*)(Args...))
{
    return std::is_same_v<T, decltype(item_at_idx<pos>(TypeList<Args...>{}))>;
}

template<size_t pos, typename T>
struct SameArgAtPos {

    template<typename Other>
    static constexpr size_t check(Other) {
        return same_arg_at<pos, T>(Other{});
    }
};

template<typename T>
T cast(Arg& a) {
    T res;
    if (!a.get(res)) {
        throw "Error: could not convert argument";
    }
    return res;
}

template<typename T, typename R, typename...Args, typename...Ready>
void call_one_ready(Arg* out, T* self, R(T::*method)(Args...), Ready&&...ready) {
    if constexpr (std::is_void_v<R>) {
        (self->*method)(std::move(ready)...);
    } else {
        out->set((self->*method)(std::move(ready)...));
    }
}

template<typename T, typename R, typename...Args, size_t...Is>
void call_one(Arg* out, T* self, Arg* args, R(T::*method)(Args...), std::index_sequence<Is...>) {
    call_one_ready(out, self, method, cast<Args>(args[Is])...);
}

template<auto first, auto...>
constexpr auto get_first() {
    return first;
}

template<size_t argc, size_t pos, typename T, auto pivot, auto...sameArg, auto...otherArg, typename...Ready>
bool choose_overload(
    Arg* out, T* self, Arg* args,
    OverloadSet<pivot, sameArg...> match,
    OverloadSet<otherArg...> miss,
    Ready&...ready)
{
    using CurrentArg = decltype(arg_at_pos<pos>(pivot));
    CurrentArg arg;
    if (args[pos].get(arg)) {
        if constexpr (pos == argc - 1) {
            call_one_ready(out, self, pivot, std::move(ready)..., arg);
            return true;
        } else {
            using NextArg =  decltype(arg_at_pos<pos + 1>(pivot));
            using Next = separated_t<SameArgAtPos<pos + 1, NextArg>, OverloadSet<pivot, sameArg...>>;
            return choose_overload<argc, pos + 1>(
                out, self, args, typename Next::pass{}, typename Next::fail{}, ready..., arg);
        }
    } else if constexpr (sizeof...(otherArg)) {
        constexpr auto new_pivot = get_first<otherArg...>();
        using ChangeArg = decltype(arg_at_pos<pos>(new_pivot));
        using ChangePivot = separated_t<SameArgAtPos<pos, ChangeArg>, OverloadSet<otherArg...>>;
        return choose_overload<argc, pos>(
            out, self, args, typename ChangePivot::pass{}, typename ChangePivot::fail{}, ready...);
    } else {
        return false;
    }
}

template<typename T, auto first, auto...rest>
bool call_any(Arg* out, T* self, Arg* args, OverloadSet<first, rest...> set) {
    constexpr size_t argc = argc_of(first);
    if constexpr (!argc || !sizeof...(rest)) {
        // special case 1: if no args -> choose first
        // case 2: if one last overload -> choose it
        call_one(out, self, args, first, std::make_index_sequence<argc>());
        return true;
    } else {
        using Arg0 = decltype(arg_at_pos<0>(first));
        using InitialSplit = separated_t<SameArgAtPos<0, Arg0>, OverloadSet<first, rest...>>;
        return choose_overload<argc, 0>(out, self, args, typename InitialSplit::pass{}, typename InitialSplit::fail{});
    }
}

template<typename T, auto...methods>
void call(Arg* out, T* self, Arg* args, size_t size, OverloadSet<methods...>) {
    constexpr size_t max_args = max_argc(methods...);
    bool hit = false;
    // lambda will be called with std::integral_constant<size_t, i>
    // for i = 0; i < max_args; ++i
    const_for_each(std::make_index_sequence<max_args + 1>(), [&](auto argc){
        if (!hit && size == argc.value) {
            using SameArgc = filtered_t<CanBeCalledWith<argc.value>, OverloadSet<methods...>>;
            if constexpr (SameArgc::count) {
                hit = call_any(out, self, args, SameArgc{});
            } else {
                throw "Error: not overload for such argument count";
            }
        }
    });
    if (!hit) {
        throw "Error: could not match any overload";
    }
}

template<size_t>
struct Test {};

struct Victim {
    int a(int a, int b) {
        return a + b;
    }
    int b(int a) {
        return a;
    }
    int c(int a, bool b) {
        return b ? a : -a;
    }
    int d(Test<0>) {
        return 1;
    }
    int d1(Test<1>) {
        return 1;
    }
    int d2(Test<2>) {
        return 1;
    }
    int d3(Test<3>) {
        return 1;
    }
    int d4(Test<4>) {
        return 1;
    }
    int d5(Test<5>) {
        return 1;
    }
    int d6(Test<6>) {
        return 1;
    }
    int d7(int, int, int, int, int, int, int, int, int, int) {
        return 1;
    }
    int d8(bool, bool, bool, bool, bool, bool, bool, bool, bool, bool) {
        return 1;
    }
    int d9(char, char, char, char, char, char, char, char, char, char) {
        return 1;
    }
    int d10(int, int, int) {
        return 1;
    }
    int d11(bool, bool, bool, bool, bool, bool) {
        return 1;
    }
    int d12(char, char, char, char, char, char, char, char) {
        return 1;
    }
};

int main()
{
    Arg out;
    Arg args[5] = {};
    using Overloads = OverloadSet<
        &Victim::a,
        &Victim::b,
        &Victim::c,
        &Victim::d,
        &Victim::d1,
        &Victim::d2,
        &Victim::d3,
        &Victim::d4,
        &Victim::d5,
        &Victim::d6,
        &Victim::d7,
        &Victim::d8,
        &Victim::d9,
        &Victim::d10,
        &Victim::d11,
        &Victim::d12>;
    Victim obj;
    call(&out, &obj, args, 1, Overloads{});
    call(&out, &obj, args, 2, Overloads{});
    return 0;
}
