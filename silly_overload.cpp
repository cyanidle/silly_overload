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

template<auto...methods>
struct OverloadSet {
    static constexpr size_t count = sizeof...(methods);
};

template<typename P, typename F>
struct SeparationResult {
    using pass = P;
    using fail = F;
};

template<typename...T>
struct concat;

template<>
struct concat<> {
    using type = OverloadSet<>;
};

template<typename T>
struct concat<T> {
    using type = T;
};

template<auto...l, auto...r, typename...Tail>
struct concat<OverloadSet<l...>, OverloadSet<r...>, Tail...> {
    using type = typename concat<OverloadSet<l..., r...>, Tail...>::type;
};

template<typename Pred, auto...methods>
using filtered_t = typename concat<std::conditional_t<Pred::check(methods), OverloadSet<methods>, OverloadSet<>>...>::type;

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

template<size_t i, typename Head, typename...Items>
struct item_at_idx {
    using type = typename item_at_idx<i - 1, Items...>::type;
};

template<typename Head, typename...Items>
struct item_at_idx<0, Head, Items...> {
    using type = Head;
};

template<size_t i, typename...Items>
using item_at_idx_t = typename item_at_idx<i, Items...>::type;

template<size_t pos, typename C, typename R, typename...Args>
auto arg_at_pos(R(C::*)(Args...)) -> item_at_idx_t<pos, Args...>;

template<size_t pos, typename T, bool is>
struct SameArgAtPos {
    template<typename C, typename R, typename...Args>
    static constexpr size_t check(R(C::*)(Args...)) {
        return std::is_same_v<T, item_at_idx_t<pos, Args...>> == is;
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

template<size_t argc, size_t pos, typename T, auto pivot, auto...other, typename...Ready>
bool choose_overload(
    Arg* out, T* self, Arg* args, OverloadSet<pivot, other...>, Ready&...ready)
{
    using CurrentArg = decltype(arg_at_pos<pos>(pivot));
    CurrentArg arg;
    if (args[pos].get(arg)) {
        if constexpr (pos == argc - 1) {
            call_one_ready(out, self, pivot, std::move(ready)..., arg);
            return true;
        } else {
            using NextArg =  decltype(arg_at_pos<pos + 1>(pivot));
            using NextSame = filtered_t<SameArgAtPos<pos + 1, NextArg, true>, pivot, other...>;
            return choose_overload<argc, pos + 1>(out, self, args, NextSame{}, ready..., arg);
        }
    } else if constexpr (sizeof...(other)) {
        using DifferentArg = filtered_t<SameArgAtPos<pos, CurrentArg, false>, other...>;
        if constexpr (DifferentArg::count) {
            return choose_overload<argc, pos>(out, self, args, DifferentArg{}, ready...);
        }
    }
    return false;
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
        return choose_overload<argc, 0>(out, self, args, set);
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
            using SameArgc = filtered_t<CanBeCalledWith<argc.value>, methods...>;
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

template<typename>
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

template<typename T>
using Overloads = OverloadSet<
    &Victim<T>::a,
    &Victim<T>::b,
    &Victim<T>::c,
    &Victim<T>::d,
    &Victim<T>::d1,
    &Victim<T>::d2,
    &Victim<T>::d3,
    &Victim<T>::d4,
    &Victim<T>::d5,
    &Victim<T>::d6,
    &Victim<T>::d7,
    &Victim<T>::d8,
    &Victim<T>::d9,
    &Victim<T>::d10,
    &Victim<T>::d11,
    &Victim<T>::d12>;

template<typename T>
void inst(Arg& out, Arg* args, size_t count) {
    Victim<T> obj;
    call(&out, &obj, args, count, Overloads<T>{});
}

template<size_t...Is>
void inst_all(Arg& out, Arg* args, std::index_sequence<Is...>) {
    (inst<Test<Is>>(out, args, Is), ...);
}

int main()
{
    Arg out;
    Arg args[20] = {};
    inst_all(out, args, std::make_index_sequence<20>());
    return 0;
}
