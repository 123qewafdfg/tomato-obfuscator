self.onmessage = async function(event) {
    const message = event.data || {};
    if (message.type !== 'process') return;

    try {
        const wasm = await import('../wasm/hilbert_image_cipher_wasm.js');
        await wasm.default();

        const method = message.method === 'block' ? wasm.CipherMethod.Block : wasm.CipherMethod.Gilbert;
        const mode = message.mode === 'decrypt' ? wasm.CipherMode.Decrypt : wasm.CipherMode.Encrypt;
        const input = new Uint8Array(message.dataBuffer);
        const output = wasm.process_rgba_rounds(
            input,
            message.width,
            message.height,
            method,
            mode,
            message.key || '',
            Math.max(1, message.blockW || 1),
            Math.max(1, message.blockH || 1),
            Math.max(1, message.rounds || 1),
            !!message.applyXor
        );

        self.postMessage({
            id: message.id,
            ok: true,
            buffer: output.buffer
        }, [output.buffer]);
    } catch (error) {
        self.postMessage({
            id: message.id,
            ok: false,
            error: error && error.message ? error.message : String(error)
        });
    }
};
