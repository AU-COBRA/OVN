from wasmtime import Store, Module, Instance, Func, FuncType, ValType, Config, Engine
import sys
import time
import os

programs = [
    "OVN.extraction.Test.ovn_test_5.wasm",
    "OVN.extraction.Test.ovn_test_10.wasm",
    "OVN.extraction.Test.ovn_test_20.wasm",
    "OVN.extraction.Test.ovn_test_100.wasm"
]
programs_c = [
    "OVN.extraction.Test.ovn_test_5.cwasm",
    "OVN.extraction.Test.ovn_test_10.cwasm",
    "OVN.extraction.Test.ovn_test_20.cwasm",
    "OVN.extraction.Test.ovn_test_100.cwasm"
]

n = 10

for program in programs:
    times_startup = []
    times_main = []

    for i in range(0,n):
        start_startup = time.time()
        config = Config()
        config.wasm_tail_call = True
        store = Store(Engine(config))

        module = Module.from_file(
            store.engine, program
        )
        # instantiate module
        instance = Instance(store, module, [])
        stop_startup = time.time()
        time_startup = round((stop_startup - start_startup) * 1000)

        # run main
        start_main = time.time()
        instance.exports(store)["main_function"](store)
        stop_main = time.time()
        time_main = round((stop_main - start_main) * 1000)
        times_startup.append(time_startup)
        times_main.append(time_main)


    print(f"{program}:\n\t{sum(times_startup)/n} ms ({times_startup}),\n\t{sum(times_main)/n} ms ({times_main})")


for program in programs_c:
    times_startup = []
    times_main = []

    for i in range(0,n):
        start_startup = time.time()
        config = Config()
        config.wasm_tail_call = True
        store = Store(Engine(config))

        module = Module.deserialize_file(
            store.engine, program
        )
        # instantiate module
        instance = Instance(store, module, [])
        stop_startup = time.time()
        time_startup = round((stop_startup - start_startup) * 1000)

        # run main
        start_main = time.time()
        instance.exports(store)["main_function"](store)
        stop_main = time.time()
        time_main = round((stop_main - start_main) * 1000)
        times_startup.append(time_startup)
        times_main.append(time_main)

    print(f"{program}:\n\t{sum(times_startup)/n} ms ({times_startup}),\n\t{sum(times_main)/n} ms ({times_main})")
