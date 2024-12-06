#include <utility>
#include <type_traits>
#include <cstddef>
#include <new>
#include <string>

template<typename T>
struct Tag {
    using type = T;
};

template<typename...Ts>
struct TypeList {
    static constexpr size_t size = sizeof...(Ts);
};

template<size_t Is, typename T>
struct ErasedTupleLeaf {
    T value;
};

template<size_t Is, typename T>
struct ErasedTupleLeaf<Is, T&> {
    T* value;
};

template<size_t I, typename T>
decltype(auto) ErasedTupleGet(ErasedTupleLeaf<I, T&>& tup) {
    return *tup.value; //NOLINT
}

template<size_t I, typename T>
decltype(auto) ErasedTupleGet(ErasedTupleLeaf<I, T>& tup) {
    return std::move(tup.value);
}

template<typename T, typename...Args>
struct _ErasedTuple;

template<size_t...Is, typename...Args>
struct _ErasedTuple<std::index_sequence<Is...>, Args...> : ErasedTupleLeaf<Is, Args>...
{};

template<typename...Args>
using ErasedTuple = _ErasedTuple<std::make_index_sequence<sizeof...(Args)>, Args...>;

template<typename...Args>
constexpr size_t erased_tuple_size_of(TypeList<Args...>) {
    return sizeof(ErasedTuple<Args...>);
}

template<typename...Args, typename...Leafs>
void erased_tuple_emplace(TypeList<Args...>, void* data, Leafs&...args) {
    new(data) ErasedTuple<Args...>{std::move(args)...};
}

template<typename...Args>
void erased_tuple_destroy(TypeList<Args...>, void* data) noexcept {
    using Tuple = ErasedTuple<Args...>;
    static_cast<Tuple*>(data)->~Tuple();
}

template<size_t I, typename...Args>
decltype(auto) erased_tuple_get(TypeList<Args...>, void* data) {
    return ErasedTupleGet<I>(*static_cast<ErasedTuple<Args...>*>(data));
}

struct Arg {
    int self{};
    template<typename T> bool get(T& v);
    template<typename T> void set(T);
};

template<typename T>
constexpr size_t _hash_type() {
    const char* src =
#ifdef _MSC_VER
        __FUNCSIG__;
#else
        __PRETTY_FUNCTION__;
#endif
    size_t result = 5381;
    char ch{};
    while((ch = *src++)) {
        result += result * 33 ^ ch;
    }
    return result;
}

template<size_t pos, typename Head, typename...Tail>
auto arg_at_pos(TypeList<Head, Tail...>) {
    if constexpr (!pos) return Tag<Head>{};
    else {
        static_assert(sizeof...(Tail));
        return arg_at_pos<pos - 1>(TypeList<Tail...>{});
    }
}

template<size_t I, typename List>
using arg_at_pos_t = typename decltype(arg_at_pos<I>(List{}))::type;

template<typename P, typename F>
struct SeparationResult {
    using pass = P;
    using fail = F;
};

template<typename Pred, class...p, class...f>
auto SeparateLists(TypeList<>, TypeList<p...>, TypeList<f...>)
    -> SeparationResult<TypeList<p...>, TypeList<f...>>;

template<typename Pred, class head, class...tail, class...p, class...f>
auto SeparateLists(TypeList<head, tail...>, TypeList<p...>, TypeList<f...>) {
    if constexpr (Pred::check(head{})) {
        return SeparateLists<Pred>(
            TypeList<tail...>{}, TypeList<p..., head>{}, TypeList<f...>{});
    } else {
        return SeparateLists<Pred>(
            TypeList<tail...>{}, TypeList<p...>{}, TypeList<f..., head>{});
    }
}

// resulting type has two typedefs
// pass: all signatures passing predicate
// fail: all signatures failing predicate
template<typename Pred, typename Set>
using separated_t = decltype(SeparateLists<Pred>(Set{}, TypeList<>{}, TypeList<>{}));

template<size_t pos, typename T>
struct SameArgAtPos {
    template<typename Other>
    static constexpr bool check(Other) {
        return std::is_same_v<T, decltype(arg_at_pos<pos>(Other{}))>;
    }
};

template<typename T, typename...Tail>
auto first(TypeList<T, Tail...>) -> T;

template<typename...Signatures>
constexpr bool conflicting_overloads = false;

template<size_t argc, size_t pos, class Pivot, class...Same, class...Other, class...Ready>
size_t choose_overload(
    void* storage, Arg* args,
    TypeList<Pivot, Same...> match,
    TypeList<Other...> miss,
    Ready&...ready)
{
    using CurrentArg = arg_at_pos_t<pos, Pivot>;
    ErasedTupleLeaf<pos, CurrentArg> arg;
    if (args[pos].get(arg.value)) {
        if constexpr (pos == argc - 1) {
            if constexpr (sizeof...(Same)) {
                static_assert(conflicting_overloads<Pivot, Same...>);
            }
            erased_tuple_emplace(Pivot{}, storage, ready..., arg);
            constexpr size_t result = _hash_type<Pivot>();
            return result;
        } else {
            using NextArg = decltype(arg_at_pos<pos + 1>(Pivot{}));
            using Next = separated_t<SameArgAtPos<pos + 1, NextArg>, TypeList<Pivot, Same...>>;
            return choose_overload<argc, pos + 1>(
                storage, args, typename Next::pass{}, typename Next::fail{}, ready..., arg);
        }
    } else if constexpr (miss.size) {
        using NewPivot = decltype(first(TypeList<Other...>{}));
        using ChangeArg = decltype(arg_at_pos<pos>(NewPivot{}));
        using ChangePivot = separated_t<SameArgAtPos<pos, ChangeArg>, TypeList<Other...>>;
        return choose_overload<argc, pos>(
            storage, args, typename ChangePivot::pass{}, typename ChangePivot::fail{}, ready...);
    } else {
        return 0;
    }
}

template<typename T> struct inspect_method;
template<typename R, typename T, typename...A>
struct inspect_method<R(T::*)(A...)>
{
    using Ret = R;
    using Cls = T;
    using Args = TypeList<A...>;
};

template<auto...methods>
struct OverloadSet {
    static constexpr size_t size = sizeof...(methods);
};

template<size_t argc>
struct CanBeCalledWith {
    template<typename...Args>
    static constexpr size_t check(TypeList<Args...> args) {
        return args.size == argc;
    }
};

template<typename R, typename T, typename...Args, size_t...Is>
bool do_call(
    Arg* out, size_t signatureHash, void* erased,
    T* self, R(T::*method)(Args...), std::index_sequence<Is...>)
{
    using Signature = TypeList<Args...>;
    constexpr size_t selfHash = _hash_type<Signature>();
    if (signatureHash == selfHash) {
        try {
            if constexpr (std::is_void_v<R>) {
                (self->*method)(erased_tuple_get<Is>(Signature{}, erased)...);
            } else {
                auto r = (self->*method)(erased_tuple_get<Is>(Signature{}, erased)...); //NOLINT
                if (out) out->set(std::move(r));
            }
            erased_tuple_destroy(Signature{}, erased);
            return true;
        } catch (...) {
            erased_tuple_destroy(Signature{}, erased);
            throw;
        }
    } else {
        return false;
    }
}

template<typename T, typename...Ts>
constexpr auto max_of(T first, Ts...v) {
    auto result = first;
    ((v > result && (result = v)), ...);
    return result;
}

template<size_t...Is, typename Fn>
constexpr void const_for_each(std::index_sequence<Is...>, Fn f) {
    (f(std::integral_constant<size_t, Is>{}), ...);
}

template<auto m>
using args_of = typename inspect_method<decltype(m)>::Args;

constexpr bool _check_signatures(const size_t* hashes, size_t count) {
    auto end = hashes + count;
    for (auto i = hashes; i != end; ++i) {
        if (!*i) return false;
        for (auto j = i + 1; j != end; ++j) {
            if (*i == *j) return false;
        }
    }
    return true;
}

template<typename T, auto...methods>
void call(Arg* out, T* self, Arg* args, size_t size, OverloadSet<methods...>) {
    constexpr size_t methods_count = sizeof...(methods);
    static_assert(methods_count, "Empty overload set");
    constexpr size_t max_args = max_of(args_of<methods>::size...);
    using ArgsListList = TypeList<args_of<methods>...>;
    constexpr size_t all_hashes[] = {_hash_type<args_of<methods>>()...};
    static_assert(_check_signatures(all_hashes, methods_count),
                  "Invalid overload signatures: Collisions found");
    constexpr auto storage_size = max_of(erased_tuple_size_of(
        typename inspect_method<decltype(methods)>::Args{})...);
    alignas(std::max_align_t) char storage[storage_size];
    size_t chosen_hash = 0; //hash for any signature must not be '0'
    // lambda will be called with std::integral_constant<size_t, i>
    // for i = 0; i < max_args; ++i
    const_for_each(std::make_index_sequence<max_args + 1>(), [&](auto argc){
        if (!chosen_hash && size == argc.value) {
            using Callable = typename separated_t<CanBeCalledWith<argc.value>, ArgsListList>::pass;
            constexpr size_t CallableCount = Callable::size;
            if constexpr (CallableCount > 0) {
                if constexpr (argc.value == 0) {
                    static_assert(Callable::size == 1 || conflicting_overloads<Callable>);
                    using Method = decltype(first(Callable{}));
                    erased_tuple_emplace(Method{}, storage);
                    constexpr size_t result = _hash_type<Method>();
                    chosen_hash = result;
                } else {
                    using First = decltype(first(Callable{}));
                    using Arg0 = decltype(arg_at_pos<0>(First{}));
                    using InitialSplit = separated_t<SameArgAtPos<0, Arg0>, Callable>;
                    chosen_hash = choose_overload<argc, 0>(
                        storage, args, typename InitialSplit::pass{}, typename InitialSplit::fail{});
                }
            } else {
                throw "Error: not overload for such argument count (argc)";
            }
        }
    });
    if (chosen_hash) {
        (do_call(out, chosen_hash, storage, self, methods, std::make_index_sequence<args_of<methods>::size>()) || ...);
    } else {
        throw "Error: could not match any overload";
    }
}

template<typename T>
bool Arg::get(T& v) {
    static int lol = 123;
    if constexpr (std::is_pointer_v<T>) {
        v = &lol;
    } else {
        v = {};
    }
    return true;
}

template<typename T>
void Arg::set(T v) {
    self = v;
}

struct Victim {
    int a(int x) {
        return x;
    }
    int b(int& x, int y) {
        return x + y;
    }
    int c(bool x) {
        return x ? 1 : -1;
    }
    int d() {
        return 1;
    }
};

int main()
{
    Arg out;
    Arg args[5] = {};
    using Overloads = OverloadSet<&Victim::a, &Victim::b, &Victim::c, &Victim::d>;
    Victim obj;
    call(&out, &obj, args, 0, Overloads{});
    call(&out, &obj, args, 1, Overloads{});
    call(&out, &obj, args, 2, Overloads{});
    return 0;
}
