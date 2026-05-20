    // 自定义弹窗函数
    function showAlert(message) {
        const alertOverlay = document.getElementById('customAlert');
        const alertMessage = document.getElementById('customAlertMessage');
        const alertBtn = document.getElementById('customAlertBtn');
        
        alertMessage.textContent = message;
        alertOverlay.style.display = 'flex';
        
        return new Promise((resolve) => {
            const handleClick = () => {
                alertOverlay.style.display = 'none';
                alertBtn.removeEventListener('click', handleClick);
                resolve();
            };
            
            alertBtn.addEventListener('click', handleClick);
        });
    }

    // 替换全局alert函数
    window.alert = showAlert;

    // Keep long-running work active on mobile. Browsers may throttle timers and
    // rendering when the screen is about to sleep or the page loses focus.
    window.mobileWorkKeepAlive = (function() {
        const state = {
            count: 0,
            wakeLock: null,
            intervalId: null,
            hadBodyTabIndex: false,
            previousBodyTabIndex: null
        };

        function focusPage() {
            try {
                if (!document.body || document.visibilityState !== 'visible') return;
                if (!state.hadBodyTabIndex) {
                    state.previousBodyTabIndex = document.body.getAttribute('tabindex');
                    document.body.setAttribute('tabindex', '-1');
                }
                window.focus();
                document.body.focus({ preventScroll: true });
            } catch (error) {
                // Some mobile browsers reject programmatic focus; Wake Lock still helps.
            }
        }

        async function requestScreenWakeLock() {
            if (!state.count || state.wakeLock || !navigator.wakeLock || document.visibilityState !== 'visible') return;
            try {
                state.wakeLock = await navigator.wakeLock.request('screen');
                state.wakeLock.addEventListener('release', () => {
                    state.wakeLock = null;
                });
            } catch (error) {
            }
        }

        function begin() {
            state.count++;
            if (state.count !== 1) return;
            state.hadBodyTabIndex = document.body && document.body.hasAttribute('tabindex');
            state.previousBodyTabIndex = document.body ? document.body.getAttribute('tabindex') : null;
            focusPage();
            requestScreenWakeLock();
            state.intervalId = window.setInterval(() => {
                focusPage();
                requestScreenWakeLock();
            }, 15000);
        }

        async function end() {
            state.count = Math.max(0, state.count - 1);
            if (state.count !== 0) return;
            if (state.intervalId) {
                window.clearInterval(state.intervalId);
                state.intervalId = null;
            }
            if (state.wakeLock) {
                try {
                    await state.wakeLock.release();
                } catch (error) {
                }
                state.wakeLock = null;
            }
            if (document.body && !state.hadBodyTabIndex) {
                document.body.removeAttribute('tabindex');
            } else if (document.body && state.previousBodyTabIndex !== null) {
                document.body.setAttribute('tabindex', state.previousBodyTabIndex);
            }
        }

        document.addEventListener('visibilitychange', () => {
            if (state.count && document.visibilityState === 'visible') {
                focusPage();
                requestScreenWakeLock();
            }
        });

        return { begin, end, poke: focusPage };
    })();

    // ==================== 视频解密模块 (IIFE) ====================
    (function() {
        "use strict";

        // ---------- 视频全局变量 ----------
        const video = document.getElementById('hidden-video');
        const canvas = document.getElementById('decodeCanvas');
        const statusEl = document.getElementById('status-text');
        const progressBar = document.getElementById('decodeProgress');
        const actionStatus = document.getElementById('actionStatus');
        let videoWidth = 0, videoHeight = 0, totalPixels = 0;
        let isDecrypting = false;
        let currentFileURL = null;
        let decMode = 'gilbert', secretKey = '', blockW = 16, blockH = 16;
        const horizontalMirror = true;      // 固定开启
        const rotateEnabled = true;
        const isMobile = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(navigator.userAgent);
        let isLandscapeVideo = false;

        // WebGL2相关
        let offscreenCanvas = null;
        let gl = null;
        let program = null;
        let uvTexture = null;
        let videoTexture = null;
        let vao = null;
        let uniformLoc = { videoSampler: null, uvSampler: null }; // 初始化为null
        let displayCtx = null;
        let currentDecryptMap = null;
        let videoFrameCallbackId = null;
        let rafDecodeId = null;
        let decodeTimeoutId = null;

        // ---------- 吉尔伯特曲线算法 (返回索引数组) ----------
        function gilbert2d(width, height) {
            const coords = [];
            if (width >= height) {
                generate(0, 0, width, 0, 0, height, coords, width);
            } else {
                generate(0, 0, 0, height, width, 0, coords, width);
            }
            return coords;
        }
        function generate(x, y, ax, ay, bx, by, coords, imgWidth) {
            const w = Math.abs(ax + ay);
            const h = Math.abs(bx + by);
            const dax = Math.sign(ax) || 0, day = Math.sign(ay) || 0;
            const dbx = Math.sign(bx) || 0, dby = Math.sign(by) || 0;
            if (h === 1) {
                for (let i = 0; i < w; i++) {
                    coords.push(y * imgWidth + x);
                    x += dax; y += day;
                }
                return;
            }
            if (w === 1) {
                for (let i = 0; i < h; i++) {
                    coords.push(y * imgWidth + x);
                    x += dbx; y += dby;
                }
                return;
            }
            let ax2 = Math.floor(ax / 2), ay2 = Math.floor(ay / 2);
            let bx2 = Math.floor(bx / 2), by2 = Math.floor(by / 2);
            if (2 * w > 3 * h) {
                if ((Math.abs(ax2 + ay2) % 2) !== 0 && w > 2) { ax2 += dax; ay2 += day; }
                generate(x, y, ax2, ay2, bx, by, coords, imgWidth);
                generate(x + ax2, y + ay2, ax - ax2, ay - ay2, bx, by, coords, imgWidth);
            } else {
                if ((Math.abs(bx2 + by2) % 2) !== 0 && h > 2) { bx2 += dbx; by2 += dby; }
                generate(x, y, bx2, by2, ax2, ay2, coords, imgWidth);
                generate(x + bx2, y + by2, ax, ay, bx - bx2, by - by2, coords, imgWidth);
                generate(x + (ax - dax) + (bx2 - dbx), y + (ay - day) + (by2 - dby),
                       -bx2, -by2, -(ax - ax2), -(ay - ay2), coords, imgWidth);
            }
        }
        function getGilbertIndices(w, h) { return new Uint32Array(gilbert2d(w, h)); }
        function getGilbertOffset(key, totalPixels) {
            if (!key) return Math.round((Math.sqrt(5) - 1) / 2 * totalPixels);
            else { let hash = 0; for (let i = 0; i < key.length; i++) hash = ((hash << 5) - hash) + key.charCodeAt(i); hash = Math.abs(hash); return hash % totalPixels; }
        }
        function buildGilbertDecryptMap(width, height, offset) {
            const total = width * height;
            const curve = getGilbertIndices(width, height);
            const rolled = new Uint32Array(total);
            for (let i = 0; i < total; i++) rolled[i] = curve[(i + offset) % total];
            const encMap = new Uint32Array(total);
            for (let i = 0; i < total; i++) encMap[curve[i]] = rolled[i];
            const map = new Uint32Array(total);
            for (let i = 0; i < total; i++) map[encMap[i]] = i;
            return map;
        }

        // ---------- 块打乱 ----------
        function simpleHash(str) { let h = 0; if (!str) return 123456; for (let i = 0; i < str.length; i++) { h = ((h << 5) - h) + str.charCodeAt(i); h |= 0; } return Math.abs(h); }
        function createSeededRNG(seed) { return function() { seed = (seed * 9301 + 49297) % 233280; return seed / 233280; } }
        function generateBlockOrder(numBlocks, key) {
            const seed = simpleHash(key);
            const rng = createSeededRNG(seed);
            const order = Array.from({length: numBlocks}, (_, i) => i);
            for (let i = order.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); [order[i], order[j]] = [order[j], order[i]]; }
            return order;
        }
        function buildBlockDecryptMap(width, height, blockW, blockH, key) {
            const cols = Math.ceil(width / blockW);
            const rows = Math.ceil(height / blockH);
            const totalBlocks = cols * rows;
            const encryptOrder = generateBlockOrder(totalBlocks, key);
            const blocks = [];
            for (let row = 0; row < rows; row++) {
                for (let col = 0; col < cols; col++) {
                    const x = col * blockW, y = row * blockH;
                    const w = Math.min(blockW, width - x), h = Math.min(blockH, height - y);
                    blocks.push({x, y, w, h, col, row, idx: row * cols + col});
                }
            }
            const decryptMap = new Uint32Array(width * height);
            for (let srcBlockIdx = 0; srcBlockIdx < totalBlocks; srcBlockIdx++) {
                const dstBlockIdx = encryptOrder[srcBlockIdx];
                const srcBlock = blocks[srcBlockIdx];
                const dstBlock = blocks[dstBlockIdx];
                for (let localY = 0; localY < srcBlock.h; localY++) {
                    for (let localX = 0; localX < srcBlock.w; localX++) {
                        const srcX = srcBlock.x + localX, srcY = srcBlock.y + localY;
                        const dstX = dstBlock.x + localX, dstY = dstBlock.y + localY;
                        if (dstX < width && dstY < height) {
                            const srcIdx = srcY * width + srcX;
                            const dstIdx = dstY * width + dstX;
                            decryptMap[srcIdx] = dstIdx;
                        }
                    }
                }
            }
            return decryptMap;
        }

        function generateRawDecryptMap() {
            if (!videoWidth || !videoHeight) throw new Error('视频尺寸未就绪');
            if (decMode === 'gilbert') {
                const offset = getGilbertOffset(secretKey, totalPixels);
                return buildGilbertDecryptMap(videoWidth, videoHeight, offset);
            } else {
                return buildBlockDecryptMap(videoWidth, videoHeight, blockW, blockH, secretKey);
            }
        }

        // ---------- WebGL2初始化 (增加错误检查) ----------
        function initWebGL() {
            if (gl) return true; // 已初始化

            offscreenCanvas = document.createElement('canvas');
            gl = offscreenCanvas.getContext('webgl2', { alpha: false, desynchronized: true, antialias: false, depth: false, stencil: false, powerPreference: 'high-performance' });
            if (!gl) { 
                statusEl.innerText = '浏览器不支持WebGL2，无法使用GPU加速'; 
                return false;
            }
            displayCtx = canvas.getContext('2d');
            if (!displayCtx) { 
                statusEl.innerText = '无法获取2D画布上下文'; 
                gl = null; // 清理
                return false;
            }

            const vsSrc = `#version 300 es
                layout(location = 0) in vec2 aPos;
                void main() {
                    gl_Position = vec4(aPos, 0.0, 1.0);
                }
            `;
            const fsSrc = `#version 300 es
                precision highp float;
                precision highp sampler2D;
                uniform sampler2D uVideoTex;
                uniform sampler2D uUvTex;
                out vec4 outColor;
                void main() {
                    ivec2 coord = ivec2(gl_FragCoord.xy);
                    vec4 uvData = texelFetch(uUvTex, coord, 0);
                    vec2 uv = uvData.rg;
                    outColor = texture(uVideoTex, uv);
                }
            `;
            const vs = gl.createShader(gl.VERTEX_SHADER);
            gl.shaderSource(vs, vsSrc);
            gl.compileShader(vs);
            if (!gl.getShaderParameter(vs, gl.COMPILE_STATUS)) {
                statusEl.innerText = '顶点着色器编译失败';
                gl = null; return false;
            }
            const fs = gl.createShader(gl.FRAGMENT_SHADER);
            gl.shaderSource(fs, fsSrc);
            gl.compileShader(fs);
            if (!gl.getShaderParameter(fs, gl.COMPILE_STATUS)) {
                statusEl.innerText = '片段着色器编译失败';
                gl = null; return false;
            }
            program = gl.createProgram();
            gl.attachShader(program, vs);
            gl.attachShader(program, fs);
            gl.linkProgram(program);
            if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
                statusEl.innerText = '着色器链接失败';
                gl = null; return false;
            }
            gl.useProgram(program);

            // 获取uniform位置并检查有效性
            uniformLoc.videoSampler = gl.getUniformLocation(program, 'uVideoTex');
            uniformLoc.uvSampler = gl.getUniformLocation(program, 'uUvTex');
            if (uniformLoc.videoSampler === null || uniformLoc.uvSampler === null) {
                statusEl.innerText = '着色器uniform获取失败';
                gl = null; return false;
            }

            const vertices = new Float32Array([-1,-1, 3,-1, -1,3]);
            const vbo = gl.createBuffer(); 
            gl.bindBuffer(gl.ARRAY_BUFFER, vbo); 
            gl.bufferData(gl.ARRAY_BUFFER, vertices, gl.STATIC_DRAW);
            vao = gl.createVertexArray(); 
            gl.bindVertexArray(vao); 
            gl.enableVertexAttribArray(0); 
            gl.vertexAttribPointer(0, 2, gl.FLOAT, false, 0, 0); 
            gl.bindVertexArray(null);

            videoTexture = gl.createTexture(); 
            gl.bindTexture(gl.TEXTURE_2D, videoTexture); 
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE); 
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE); 
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR); 
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR); 
            gl.bindTexture(gl.TEXTURE_2D, null);

            uvTexture = gl.createTexture(); 
            gl.bindTexture(gl.TEXTURE_2D, uvTexture); 
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE); 
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE); 
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST); 
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST); 
            gl.bindTexture(gl.TEXTURE_2D, null);

            statusEl.innerText = 'WebGL2就绪 (离屏渲染)';
            return true;
        }

        function updateUvTextureFromMap(map, width, height) {
            if (!gl || !uvTexture) return;
            const total = width * height;
            const uvData = new Float32Array(total * 4);
            for (let dstIdx = 0; dstIdx < total; dstIdx++) {
                const srcIdx = map[dstIdx];
                const srcX = srcIdx % width;
                const srcY = Math.floor(srcIdx / width);
                const u = (srcX + 0.5) / width;
                const v = (srcY + 0.5) / height;
                uvData[dstIdx*4] = u; uvData[dstIdx*4+1] = v;
            }
            gl.bindTexture(gl.TEXTURE_2D, uvTexture);
            gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA32F, width, height, 0, gl.RGBA, gl.FLOAT, uvData);
            gl.bindTexture(gl.TEXTURE_2D, null);
        }

        function webglRenderFrame() {
            if (!gl || !program || !video.videoWidth) return false;
            // 确保uniform位置有效
            if (uniformLoc.videoSampler === null || uniformLoc.uvSampler === null) return false;

            if (offscreenCanvas.width !== video.videoWidth || offscreenCanvas.height !== video.videoHeight) {
                offscreenCanvas.width = video.videoWidth; offscreenCanvas.height = video.videoHeight;
                canvas.width = video.videoWidth; canvas.height = video.videoHeight;
                gl.viewport(0, 0, offscreenCanvas.width, offscreenCanvas.height);
            }
            gl.activeTexture(gl.TEXTURE0); 
            gl.bindTexture(gl.TEXTURE_2D, videoTexture); 
            gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, video);
            gl.activeTexture(gl.TEXTURE1); 
            gl.bindTexture(gl.TEXTURE_2D, uvTexture);
            gl.useProgram(program); 
            // 设置uniform sampler值
            gl.uniform1i(uniformLoc.videoSampler, 0); 
            gl.uniform1i(uniformLoc.uvSampler, 1);
            gl.bindVertexArray(vao); 
            gl.drawArrays(gl.TRIANGLES, 0, 3); 
            gl.bindVertexArray(null);
            // 后处理：旋转180°固定 + 水平镜像强制
            displayCtx.clearRect(0, 0, canvas.width, canvas.height);
            displayCtx.save();
            const w = canvas.width, h = canvas.height;
            displayCtx.translate(w/2, h/2);
            displayCtx.scale(-1, 1);        // 水平镜像强制
            displayCtx.rotate(Math.PI);      // 旋转180°固定
            displayCtx.drawImage(offscreenCanvas, -w/2, -h/2, w, h);
            displayCtx.restore();
            return true;
        }

        function cancelScheduledDecodeFrame() {
            if (videoFrameCallbackId !== null && typeof video.cancelVideoFrameCallback === 'function') {
                try {
                    video.cancelVideoFrameCallback(videoFrameCallbackId);
                } catch (error) {
                }
                videoFrameCallbackId = null;
            }
            if (rafDecodeId !== null && typeof cancelAnimationFrame === 'function') {
                cancelAnimationFrame(rafDecodeId);
                rafDecodeId = null;
            }
            if (decodeTimeoutId !== null) {
                window.clearTimeout(decodeTimeoutId);
                decodeTimeoutId = null;
            }
        }

        function renderDecodeFrame() {
            if (!isDecrypting || video.paused || video.ended) return false;
            webglRenderFrame();
            if (video.duration) progressBar.value = (video.currentTime / video.duration) * 100;
            return true;
        }

        function scheduleDecodeFrame() {
            cancelScheduledDecodeFrame();
            if (!isDecrypting || video.paused || video.ended) return;
            let fired = false;
            const run = () => {
                if (fired) return;
                fired = true;
                const shouldContinue = renderDecodeFrame();
                cancelScheduledDecodeFrame();
                if (shouldContinue) scheduleDecodeFrame();
            };
            if (typeof video.requestVideoFrameCallback === 'function') {
                videoFrameCallbackId = video.requestVideoFrameCallback(run);
            }
            if (typeof requestAnimationFrame === 'function') {
                rafDecodeId = requestAnimationFrame(run);
            }
            decodeTimeoutId = window.setTimeout(run, 33);
        }

        function stopDecoding() {
            const wasDecrypting = isDecrypting;
            isDecrypting = false;
            cancelScheduledDecodeFrame();
            if (video) video.pause();
            if (wasDecrypting && window.mobileWorkKeepAlive) window.mobileWorkKeepAlive.end();
        }
        window.videoStopDecoding = stopDecoding;   // 供tab切换调用

        function startDecode() {
            if (!video.src) { statusEl.innerText = '请先选择视频'; actionStatus.innerText = '当前未导入视频，请选择解密状态'; return; }
            if (!video.videoWidth) { statusEl.innerText = '视频未完全加载'; return; }
            stopDecoding();
            videoWidth = video.videoWidth; videoHeight = video.videoHeight;
            totalPixels = videoWidth * videoHeight;
            canvas.width = videoWidth; canvas.height = videoHeight;
            if (offscreenCanvas) { offscreenCanvas.width = videoWidth; offscreenCanvas.height = videoHeight; }
            if (!initWebGL()) { 
                statusEl.innerText = 'WebGL2初始化失败，无法解密'; 
                return; 
            }
            try { 
                currentDecryptMap = generateRawDecryptMap(); 
            } catch (e) { 
                statusEl.innerText = '映射生成失败'; 
                return; 
            }
            updateUvTextureFromMap(currentDecryptMap, videoWidth, videoHeight);
            isDecrypting = true;
            if (window.mobileWorkKeepAlive) window.mobileWorkKeepAlive.begin();
            actionStatus.innerText = '已选定解密模式，正在解密中';
            video.play().then(() => {
                scheduleDecodeFrame();
                statusEl.innerText = '解密播放中';
            }).catch((e) => { 
                isDecrypting = false; 
                if (window.mobileWorkKeepAlive) window.mobileWorkKeepAlive.end();
                statusEl.innerText = '播放失败: ' + e.message; 
                actionStatus.innerText = '已选择解密状态，请确认解密模式。';
            });
            video.onended = () => {
                cancelScheduledDecodeFrame();
                if (isDecrypting && window.mobileWorkKeepAlive) window.mobileWorkKeepAlive.end();
                isDecrypting = false;
                statusEl.innerText = '播放结束';
                actionStatus.innerText = '已选择解密状态，请确认解密模式。';
            };
        }

        // 事件绑定
        document.getElementById('videoFileInput').addEventListener('change', function(e) {
            const file = e.target.files[0]; if (!file) return;
            stopDecoding();
            if (currentFileURL) URL.revokeObjectURL(currentFileURL);
            currentFileURL = URL.createObjectURL(file);
            video.src = currentFileURL; video.load(); video.pause();
            statusEl.innerText = '视频加载中...';
            actionStatus.innerText = '已选择解密状态，请确认解密模式。';
            video.onloadedmetadata = () => {
                videoWidth = video.videoWidth;
                videoHeight = video.videoHeight;
                if (videoWidth && videoHeight) {
                    canvas.width = videoWidth;
                    canvas.height = videoHeight;
                    if (offscreenCanvas) { offscreenCanvas.width = videoWidth; offscreenCanvas.height = videoHeight; }
                    document.getElementById('video-dim').innerText = `${videoWidth}x${videoHeight}`;
                    // 检测是否为横屏视频
                    isLandscapeVideo = videoWidth > videoHeight;
                    statusEl.innerText = '视频就绪，可点击解密执行';
                    actionStatus.innerText = '已选择解密状态，请确认解密模式。';
                }
            };
            video.onerror = () => { statusEl.innerText = '视频加载失败'; actionStatus.innerText = '当前未导入视频，请选择解密状态'; };
        });
        document.getElementById('startDecodeBtn').addEventListener('click', startDecode);
        // 下载工具按钮事件
        document.getElementById('downloadToolBtn').addEventListener('click', () => {
            document.getElementById('downloadModal').style.display = 'flex';
        });

        // 关闭下载弹窗事件
        document.getElementById('closeDownloadModalBtn').addEventListener('click', () => {
            document.getElementById('downloadModal').style.display = 'none';
        });

        document.getElementById('closeDownloadModalBtnBottom').addEventListener('click', () => {
            document.getElementById('downloadModal').style.display = 'none';
        });

        // 点击遮罩关闭弹窗
        document.getElementById('downloadModal').addEventListener('click', (e) => {
            if (e.target === document.getElementById('downloadModal')) {
                document.getElementById('downloadModal').style.display = 'none';
            }
        });

        document.getElementById('paramBtn').addEventListener('click', () => {
            document.querySelector(`input[name="decMode"][value="${decMode}"]`).checked = true;
            document.getElementById('keyInput').value = secretKey;
            document.getElementById('blockWidth').value = blockW;
            document.getElementById('blockHeight').value = blockH;
            document.getElementById('blockWidthRow').style.display = decMode==='block'?'flex':'none';
            document.getElementById('blockHeightRow').style.display = decMode==='block'?'flex':'none';
            document.getElementById('paramModal').style.display = 'flex';
        });
        document.querySelectorAll('input[name="decMode"]').forEach(r => r.addEventListener('change', function(e) {
            const mode = e.target.value;
            document.getElementById('blockWidthRow').style.display = mode==='block'?'flex':'none';
            document.getElementById('blockHeightRow').style.display = mode==='block'?'flex':'none';
        }));
        document.getElementById('closeParamBtn').addEventListener('click', () => {
            decMode = document.querySelector('input[name="decMode"]:checked').value;
            secretKey = document.getElementById('keyInput').value;
            blockW = parseInt(document.getElementById('blockWidth').value,10) || 16;
            blockH = parseInt(document.getElementById('blockHeight').value,10) || 16;
            document.getElementById('paramModal').style.display = 'none';
            statusEl.innerText = video.src ? '参数已更新' : '请先选择视频';
            actionStatus.innerText = video.src ? '已选定解密模式，正在解密中' : '当前未导入视频，请选择解密状态';
        });
        window.addEventListener('click', (e) => { if (e.target === document.getElementById('paramModal')) document.getElementById('paramModal').style.display = 'none'; });

        // 进度条拖动
        let seeking = false;
        progressBar.addEventListener('mousedown',()=>{ seeking = true; });
        progressBar.addEventListener('input', function(e) { if(video.duration) video.currentTime = (e.target.value/100)*video.duration; });
        progressBar.addEventListener('mouseup', ()=>{ seeking = false; });
        video.addEventListener('timeupdate', ()=>{ if(!seeking && video.duration) progressBar.value = (video.currentTime/video.duration)*100; });

        // 双击进入/退出全屏
        let clickCount = 0;
        let clickTimer = null;
        document.getElementById('canvasFullscreenWrapper').addEventListener('click', () => {
            clickCount++;
            if (clickCount === 1) {
                clickTimer = setTimeout(() => {
                    clickCount = 0;
                }, 300);
            } else if (clickCount === 2) {
                clearTimeout(clickTimer);
                clickCount = 0;
                const wrap = document.getElementById('canvasFullscreenWrapper');
                if (!document.fullscreenElement) {
                    // 进入全屏
                    wrap.requestFullscreen().then(() => {
                    }).catch(err => {
                    });
                } else {
                    // 退出全屏
                    document.exitFullscreen();
                }
            }
        });

        // 全屏滑动控制
        let touchStartX = 0;
        let touchStartTime = 0;
        const swipeThreshold = 50; // 最小滑动距离
        const swipeTimeThreshold = 500; // 最大滑动时间
        
        function handleSwipe(deltaX, deltaTime) {
            if (Math.abs(deltaX) < swipeThreshold || deltaTime > swipeTimeThreshold) return;
            
            // 计算滑动速度和距离，映射到秒数
            const swipeSpeed = Math.abs(deltaX) / deltaTime; // 像素/毫秒
            const seekSeconds = Math.max(1, Math.min(10, Math.floor(Math.abs(deltaX) / 50)));
            
            if (deltaX > 0) {
                // 向右滑动，快进
                video.currentTime = Math.min(video.duration, video.currentTime + seekSeconds);
            } else {
                // 向左滑动，回退
                video.currentTime = Math.max(0, video.currentTime - seekSeconds);
            }
        }

        // 鼠标事件
        canvas.addEventListener('mousedown', (e) => {
            if (!document.fullscreenElement) return;
            touchStartX = e.clientX;
            touchStartTime = Date.now();
        });

        canvas.addEventListener('mouseup', (e) => {
            if (!document.fullscreenElement) return;
            const touchEndX = e.clientX;
            const touchEndTime = Date.now();
            const deltaX = touchEndX - touchStartX;
            const deltaTime = touchEndTime - touchStartTime;
            handleSwipe(deltaX, deltaTime);
        });

        // 触摸事件（仅滑动控制，禁止双指缩放）
        canvas.addEventListener('touchstart', (e) => {
            if (!document.fullscreenElement) return;
            touchStartX = e.touches[0].clientX;
            touchStartTime = Date.now();
        }, { passive: true });

        canvas.addEventListener('touchmove', (e) => {
            if (!document.fullscreenElement) return;
        }, { passive: false });

        canvas.addEventListener('touchend', (e) => {
            if (!document.fullscreenElement) return;
            if (e.changedTouches.length > 0) {
                const touchEndX = e.changedTouches[0].clientX;
                const touchEndTime = Date.now();
                const deltaX = touchEndX - touchStartX;
                const deltaTime = touchEndTime - touchStartTime;
                handleSwipe(deltaX, deltaTime);
            }
        });



        // 监听全屏状态变化
        document.addEventListener('fullscreenchange', () => {
            if (document.fullscreenElement) {
                // 进入全屏
                if (isMobile && isLandscapeVideo) {
                    // 对于移动设备横屏视频，强制横屏显示
                    const fullscreenElement = document.fullscreenElement;
                    if (fullscreenElement) {
                        // 保存原始样式
                        fullscreenElement.dataset.originalStyle = fullscreenElement.style.cssText;
                        
                        // 应用横屏样式
                        fullscreenElement.style.width = '100%';
                        fullscreenElement.style.height = '100%';
                        fullscreenElement.style.objectFit = 'contain';
                        
                        // 调整body
                        document.body.style.orientation = 'landscape';
                        document.body.style.width = '100%';
                        document.body.style.height = '100%';
                        document.body.style.margin = '0';
                        document.body.style.padding = '0';
                        document.body.style.overflow = 'hidden';
                    }
                }
            } else {
                // 退出全屏
                // 恢复全屏元素样式
                const wrap = document.getElementById('canvasFullscreenWrapper');
                if (wrap.dataset.originalStyle) {
                    wrap.style.cssText = wrap.dataset.originalStyle;
                    delete wrap.dataset.originalStyle;
                }

                // 恢复body样式
                document.body.style.orientation = '';
                document.body.style.width = '';
                document.body.style.height = '';
                document.body.style.margin = '';
                document.body.style.padding = '';
                document.body.style.overflow = '';
            }
        });

        window.addEventListener('beforeunload', () => { if (currentFileURL) URL.revokeObjectURL(currentFileURL); });
        // 水平镜像强制开启
        const mirrorV = document.getElementById('horizontalMirrorVideo'); if (mirrorV) mirrorV.checked = true;
    })();

    // ==================== 图片解密模块 (IIFE) ====================
    (function() {
        "use strict";
        // 图片页面元素
        const imagePicker = document.getElementById('imageFilePicker');
        const browseBtn = document.getElementById('browseImages');
        const viewPreviewBtn = document.getElementById('viewPreviewBtn');
        const previewModal = document.getElementById('previewModal');
        const prevBtn = document.getElementById('prevPreviewBtn');
        const nextBtn = document.getElementById('nextPreviewBtn');
        const previewImg = document.getElementById('previewImg');
        const previewCounter = document.getElementById('previewCounter');
        const startEncrypt = document.getElementById('startEncryptImg');
        const startDecrypt = document.getElementById('startDecryptImg');
        const keyInput = document.getElementById('keyInputImg');
        const exportConfigBtn = document.getElementById('exportConfigImg');
        const downloadAllBtn = document.getElementById('downloadAllBtn');
        const chooseMethodBtn = document.getElementById('methodInfoClickable');
        const currentMethodDisplay = document.getElementById('currentMethodDisplay');
        const encryptMethodModal = document.getElementById('encryptMethodModal');
        const imgEncryptRadios = document.querySelectorAll('input[name="imgEncryptMode"]');
        const imgBlockParamsDiv = document.getElementById('imgBlockParams');
        const imgBlockWidthSelect = document.getElementById('imgBlockWidthSelect');
        const imgBlockHeightSelect = document.getElementById('imgBlockHeightSelect');
        const imgFastestParamsDiv = document.getElementById('imgFastestParams');
        const standardizeBtn = document.getElementById('standardizeBtn');
        const saveEncryptMethodBtn = document.getElementById('saveEncryptMethodBtn');
        const blockHint = document.getElementById('blockHint');
        const packCheck = document.getElementById('packDownload');
        const exportKeyCheck = document.getElementById('exportKeyFileCheckbox');
        const imgFormatSelect = document.getElementById('imgFormat');
        const batchFormatSelect = document.getElementById('batchFormat');
        const imageProgress = document.getElementById('imageProgress');
        const selectedCountDisplay = document.getElementById('selectedCountDisplay');
        const resetBtn = document.getElementById('resetToOriginalBtn');
        const reencryptToggleBtn = document.getElementById('reencryptToggleBtn');
        const mirrorImg = document.getElementById('horizontalMirrorImage'); if (mirrorImg) mirrorImg.checked = true;
        const xorToggle = document.getElementById('xorToggle');
        const largeImageWarningToggle = document.getElementById('largeImageWarningToggle');
        const largeImageWarningHelp = document.getElementById('largeImageWarningHelp');
        const imageCompatNote = document.getElementById('imageCompatNote');
        const imageSpeedStatus = document.getElementById('imageSpeedStatus');
        const imageSpeedStatusText = document.getElementById('imageSpeedStatusText');
        // 图片入口强约束：这个文件选择器只用于导入图片。
        // 即使 HTML 已写 accept，这里也在 JS 初始化时再强制一遍，避免后续改动或浏览器行为导致用户选到非图片。
        if (imagePicker) {
            imagePicker.setAttribute('accept', 'image/*');
            imagePicker.setAttribute('multiple', 'multiple');
        }

        // 状态变量
        let selectedImageFiles = [];
        let previewUrls = [];
        let currentPreviewIndex = 0;
        let imgMethod = 'gilbert';
        let imgBlockW = 1, imgBlockH = 1;
        const IMAGE_METHOD_SETTINGS_STORAGE_KEY = 'imageMethodSettings';
        let latestProcessedImages = [];
        let latestKeyParams = null;
        let isProcessing = false;
        let isReencryptEnabled = false;
        const XOR_FIXED_KEY = 255;
        const XOR_ENABLED_STORAGE_KEY = 'imageColorInvertEnabled';
        const LARGE_IMAGE_PIXEL_LIMIT = 1080 * 1920;
        const QUICK_IMAGE_DIMENSION_HEADER_BYTES = 256;
        const LARGE_IMAGE_DIMENSION_HEADER_BYTES = 512 * 1024;
        const LARGE_IMAGE_WARNING_STORAGE_KEY = 'largeImageImportWarningEnabled';
        const IS_MOBILE_IMAGE_PROCESSING = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(navigator.userAgent);
        const IMAGE_PROCESSING_CHUNK_PIXELS = IS_MOBILE_IMAGE_PROCESSING ? 32768 : 262144;
        const GPU_REMAP_MIN_PIXELS = IS_MOBILE_IMAGE_PROCESSING ? 512 * 512 : 1024 * 1024;
        const GPU_REMAP_MAX_PACKED_INDEX = 16777215;
        const WORKER_REMAP_MIN_PIXELS = IS_MOBILE_IMAGE_PROCESSING ? 256 * 256 : 512 * 512;
        let imageGpuRemapAvailable = null;
        let imageRemapWorkerAvailable = typeof Worker === 'function' && typeof Blob === 'function' && typeof URL !== 'undefined';
        let imageRemapWorker = null;
        let imageRemapWorkerUrl = null;
        let imageRemapWorkerJobId = 0;
        const imageRemapWorkerJobs = new Map();
        let isXOREnabled = localStorage.getItem(XOR_ENABLED_STORAGE_KEY) === '1';
        let isLargeImageWarningEnabled = localStorage.getItem(LARGE_IMAGE_WARNING_STORAGE_KEY) === '1';
        let xorAppliedForEncrypt = false;
        let xorAppliedForDecrypt = false;
        let largeImageInfos = [];
        let latestLargeImageImportChoice = 'keep';
        let cachedFirstImageWidth = null, cachedFirstImageHeight = null, cachedFirstImageName = '';
        const mapCache = new Map();
        const MAP_CACHE_LIMIT = 2;
        let encryptCount = 0;
        let xorCompatibilityReady = Promise.resolve();
        let batchXORStateOverride = null;
        let imageImportSequence = 0;
        const imageRuntime = {
            hasOffscreenCanvas: typeof OffscreenCanvas === 'function' && typeof OffscreenCanvas.prototype.convertToBlob === 'function',
            hasCreateImageBitmap: typeof createImageBitmap === 'function',
            webpTranscodeSupported: null
        };
        const IMAGE_CIPHER_WASM_URL = new URL('../wasm/hilbert_image_cipher_wasm.js', document.currentScript && document.currentScript.src ? document.currentScript.src : window.location.href).href;
        const IMAGE_CIPHER_WORKER_URL = new URL('image-wasm-worker.js', document.currentScript && document.currentScript.src ? document.currentScript.src : window.location.href).href;
        const JSZIP_URL = new URL('jszip.min.js', document.currentScript && document.currentScript.src ? document.currentScript.src : window.location.href).href;
        let imageCipherWasmPromise = null;
        let imageCipherWasmAvailable = true;
        let imageCipherWorkerAvailable = typeof Worker === 'function';
        let imageCipherWorker = null;
        let imageCipherWorkerJobId = 0;
        const imageCipherWorkerJobs = new Map();
        let jsZipPromise = null;
        const IMAGE_CIPHER_DEBUG_PREFIX = '[WASM-CIPHER]';
        let imageCipherSuccessEffectsStarted = false;
        xorToggle.checked = isXOREnabled;
        if (largeImageWarningToggle) largeImageWarningToggle.checked = isLargeImageWarningEnabled;

        // XOR 开关事件监听
        xorToggle.addEventListener('change', function() {
            if (this.disabled) {
                this.checked = false;
                isXOREnabled = false;
                localStorage.setItem(XOR_ENABLED_STORAGE_KEY, '0');
                return;
            }
            isXOREnabled = this.checked;
            localStorage.setItem(XOR_ENABLED_STORAGE_KEY, isXOREnabled ? '1' : '0');
        });
        if (largeImageWarningToggle) {
            largeImageWarningToggle.addEventListener('change', function() {
                isLargeImageWarningEnabled = this.checked;
                localStorage.setItem(LARGE_IMAGE_WARNING_STORAGE_KEY, isLargeImageWarningEnabled ? '1' : '0');
            });
        }
        if (largeImageWarningHelp) {
            largeImageWarningHelp.addEventListener('click', showLargeImageWarningHelp);
        }

        function setImageSpeedStatus(status) {
            if (!imageSpeedStatus || !imageSpeedStatusText) return;
            imageSpeedStatus.classList.remove('pending', 'ready', 'compat');
            imageSpeedStatus.classList.add(status);
            if (status === 'ready') {
                imageSpeedStatusText.textContent = '高速处理已开启';
                imageSpeedStatus.dataset.message = '您的设备非常的好，可以使用本网站的高速模式，感谢您的使用';
            } else if (status === 'compat') {
                imageSpeedStatusText.textContent = '低速处理待命';
                imageSpeedStatus.dataset.message = '您的设备非常之垃圾，估计是10年前的破铜烂铁，所以你没有资格使用高速模式，非常不感谢您的使用';
            } else {
                imageSpeedStatusText.textContent = imageCipherWorkerAvailable ? '高速处理待命' : '兼容模式待命';
                imageSpeedStatus.dataset.message = imageCipherWorkerAvailable
                    ? '您的设备非常的好，可以使用本网站的高速模式，感谢您的使用'
                    : '您的设备非常之垃圾，估计是10年前的破铜烂铁，所以你没有资格使用高速模式，非常不感谢您的使用';
            }
        }

        function showImageSpeedStatusMessage() {
            alert(imageSpeedStatus && imageSpeedStatus.dataset.message
                ? imageSpeedStatus.dataset.message
                : '您的设备非常之垃圾，估计是10年前的破铜烂铁。所以你没有资格使用高速模式，非常不感谢您的使用。');
        }

        if (imageSpeedStatus) {
            imageSpeedStatus.addEventListener('click', showImageSpeedStatusMessage);
            imageSpeedStatus.addEventListener('touchend', (event) => {
                event.preventDefault();
                showImageSpeedStatusMessage();
            }, { passive: false });
        }
        document.addEventListener('click', (event) => {
            const target = event.target && event.target.closest ? event.target.closest('#imageSpeedStatus') : null;
            if (target && target !== imageSpeedStatus) showImageSpeedStatusMessage();
        });
        setImageSpeedStatus(imageCipherWorkerAvailable ? 'pending' : 'compat');

        function getMapCache(cacheKey) {
            const cached = mapCache.get(cacheKey);
            if (!cached) return null;
            mapCache.delete(cacheKey);
            mapCache.set(cacheKey, cached);
            return cached;
        }

        function setMapCache(cacheKey, value) {
            if (mapCache.has(cacheKey)) {
                mapCache.delete(cacheKey);
            }
            mapCache.set(cacheKey, value);
            while (mapCache.size > MAP_CACHE_LIMIT) {
                const oldestKey = mapCache.keys().next().value;
                if (oldestKey === undefined) break;
                mapCache.delete(oldestKey);
            }
            return value;
        }

        function clearTransientImageCache() {
            mapCache.clear();
        }

        function initImageCipherWasm() {
            if (!imageCipherWasmAvailable) {
                return null;
            }
            if (!imageCipherWasmPromise) {
                imageCipherWasmPromise = import(IMAGE_CIPHER_WASM_URL)
                    .then(async (module) => {
                        await module.default();
                        startImageCipherSuccessEffects();
                        return module;
                    })
                    .catch((error) => {
                        imageCipherWasmAvailable = false;
                        return null;
                    });
            } else {
                }
            return imageCipherWasmPromise;
        }

        function getImageCipherWorker() {
            if (!imageCipherWorkerAvailable) return null;
            if (imageCipherWorker) return imageCipherWorker;
            try {
                imageCipherWorker = new Worker(IMAGE_CIPHER_WORKER_URL, { type: 'module' });
                imageCipherWorker.onmessage = function(event) {
                    const message = event.data || {};
                    const job = imageCipherWorkerJobs.get(message.id);
                    if (!job) return;
                    imageCipherWorkerJobs.delete(message.id);
                    if (message.ok) job.resolve(new Uint8ClampedArray(message.buffer));
                    else job.reject(new Error(message.error || 'Image cipher worker failed'));
                };
                imageCipherWorker.onerror = function(error) {
                    const pendingJobs = Array.from(imageCipherWorkerJobs.values());
                    imageCipherWorkerJobs.clear();
                    imageCipherWorkerAvailable = false;
                    imageCipherWorker = null;
                    pendingJobs.forEach(job => job.reject(new Error(error && error.message ? error.message : 'Image cipher worker failed')));
                };
                return imageCipherWorker;
            } catch (error) {
                imageCipherWorkerAvailable = false;
                return null;
            }
        }

        function processImagePixelsInWasmWorker(data, request, keyStr) {
            const worker = getImageCipherWorker();
            if (!worker) return null;
            const jobId = ++imageCipherWorkerJobId;
            const input = new Uint8Array(data);
            return new Promise((resolve, reject) => {
                imageCipherWorkerJobs.set(jobId, { resolve, reject });
                try {
                    worker.postMessage({
                        type: 'process',
                        id: jobId,
                        dataBuffer: input.buffer,
                        width: request.width,
                        height: request.height,
                        method: request.method,
                        mode: request.mode,
                        key: keyStr || '',
                        blockW: request.blockW,
                        blockH: request.blockH,
                        rounds: request.rounds,
                        applyXor: request.shouldApplyXOR
                    }, [input.buffer]);
                } catch (error) {
                    imageCipherWorkerJobs.delete(jobId);
                    reject(error);
                }
            });
        }

        async function processImagePixelsWithWasm(data, width, height, mode, blockW, blockH, keyStr, rounds, shouldApplyXOR) {
            const startedAt = performance.now();
            const request = {
                mode,
                method: imgMethod,
                width,
                height,
                pixels: width * height,
                bytes: data ? data.length : 0,
                blockW: Math.max(1, blockW || 1),
                blockH: Math.max(1, blockH || 1),
                keyLength: keyStr ? keyStr.length : 0,
                keyHash: simpleHash(keyStr || ''),
                rounds: Math.max(1, rounds || 1),
                shouldApplyXOR: !!shouldApplyXOR
            };
            const workerResultPromise = processImagePixelsInWasmWorker(data, request, keyStr);
            if (workerResultPromise) {
                try {
                    const result = await workerResultPromise;
                    setImageSpeedStatus('ready');
                    startImageCipherSuccessEffects();
                    return result;
                } catch (error) {
                    imageCipherWorkerAvailable = false;
                    setImageSpeedStatus('compat');
                }
            }
            const wasm = await initImageCipherWasm();
            if (!wasm) {
                return null;
            }
            const method = imgMethod === 'block' ? wasm.CipherMethod.Block : wasm.CipherMethod.Gilbert;
            const wasmMode = mode === 'decrypt' ? wasm.CipherMode.Decrypt : wasm.CipherMode.Encrypt;
            const output = wasm.process_rgba_rounds(
                data,
                width,
                height,
                method,
                wasmMode,
                keyStr,
                Math.max(1, blockW || 1),
                Math.max(1, blockH || 1),
                Math.max(1, rounds || 1),
                !!shouldApplyXOR
            );
            const result = output instanceof Uint8ClampedArray ? output : new Uint8ClampedArray(output.buffer, output.byteOffset, output.byteLength);
            setImageSpeedStatus(imageCipherWorkerAvailable ? 'ready' : 'compat');
            return result;
        }

        function startImageCipherSuccessEffects() {
            if (imageCipherSuccessEffectsStarted) return;
            imageCipherSuccessEffectsStarted = true;
            startWasmButtonFlipEffect();
            startWasmGoldPixiEffect();
        }

        function startWasmButtonFlipEffect() {
            if (!window.gsap) {
                return;
            }
            const buttons = [startEncrypt, startDecrypt].filter(Boolean);
            if (!buttons.length) return;
            buttons.forEach(button => button.classList.add('wasm-cipher-effect-ready'));
            window.gsap.set(buttons, {
                transformPerspective: 700,
                transformOrigin: '50% 50%',
                backfaceVisibility: 'hidden'
            });
            window.gsap.fromTo(buttons, {
                rotationY: 0
            }, {
                rotationY: 360,
                duration: 0.5,
                ease: 'power2.inOut',
                stagger: 0.018,
                overwrite: 'auto',
                clearProps: 'rotationY'
            });
            }

        async function startWasmGoldPixiEffect() {
            if (!window.PIXI) {
                return;
            }
            try {
                const PIXI = window.PIXI;
                const targets = [startEncrypt, startDecrypt].filter(Boolean);
                let started = 0;
                for (const button of targets) {
                    const app = new PIXI.Application();
                    await app.init({
                        width: 1,
                        height: 1,
                        backgroundAlpha: 0,
                        antialias: true,
                        autoDensity: true,
                        resolution: Math.min(window.devicePixelRatio || 1, 2)
                    });
                    app.canvas.style.position = 'absolute';
                    app.canvas.style.inset = '0';
                    app.canvas.style.width = '100%';
                    app.canvas.style.height = '100%';
                    app.canvas.style.pointerEvents = 'none';
                    app.canvas.style.zIndex = '1';
                    app.canvas.style.mixBlendMode = 'screen';
                    app.canvas.setAttribute('aria-hidden', 'true');
                    button.classList.add('wasm-cipher-effect-ready');
                    button.appendChild(app.canvas);

                    const sweep = new PIXI.Graphics();
                    const halo = new PIXI.Graphics();
                    const sparkles = new PIXI.Graphics();
                    app.stage.addChild(halo, sweep, sparkles);

                    const gold = 0xffd36a;
                    const paleGold = 0xfff2b7;
                    const deepGold = 0xd4982f;
                    let tick = started * 0.35;

                    app.ticker.add(() => {
                        tick += app.ticker.deltaMS / 1000;
                        const rect = button.getBoundingClientRect();
                        const w = Math.max(1, Math.round(rect.width));
                        const h = Math.max(1, Math.round(rect.height));
                        if (app.renderer.width !== w * app.renderer.resolution || app.renderer.height !== h * app.renderer.resolution) {
                            app.renderer.resize(w, h);
                        }
                        const diagonal = Math.hypot(w, h);
                        const travel = (tick * 120) % (w + 220);
                        const x = travel - 110;

                        halo.clear();
                        halo.circle(w * 0.18 + Math.sin(tick * 0.65) * 8, h * 0.18, h * 0.85).fill({ color: gold, alpha: 0.18 });
                        halo.circle(w * 0.82 + Math.cos(tick * 0.5) * 8, h * 0.78, h * 0.95).fill({ color: deepGold, alpha: 0.13 });

                        sweep.clear();
                        sweep.rotation = -0.46;
                        sweep.x = x;
                        sweep.y = h + 40;
                        sweep.rect(0, -diagonal, 12, diagonal * 2).fill({ color: paleGold, alpha: 0.34 });
                        sweep.rect(16, -diagonal, 42, diagonal * 2).fill({ color: gold, alpha: 0.16 });
                        sweep.rect(66, -diagonal, 9, diagonal * 2).fill({ color: paleGold, alpha: 0.24 });

                        sparkles.clear();
                        for (let i = 0; i < 8; i++) {
                            const px = (i * 37 + tick * 18) % (w + 20) - 10;
                            const py = (i * 19 + Math.sin(tick + i) * 8) % (h + 10) - 5;
                            const radius = 0.9 + ((i % 3) * 0.45) + Math.sin(tick * 2 + i) * 0.2;
                            sparkles.circle(px, py, radius).fill({ color: i % 3 ? gold : paleGold, alpha: 0.35 });
                        }
                    });
                    started++;
                }
                } catch (error) {
                }
        }

        function yieldToBrowser() {
            maintainImageProcessingActivity();
            return new Promise(resolve => {
                if (!IS_MOBILE_IMAGE_PROCESSING && window.scheduler && typeof window.scheduler.yield === 'function') {
                    window.scheduler.yield().then(resolve, resolve);
                    return;
                }
                if (typeof MessageChannel === 'function') {
                    const channel = new MessageChannel();
                    let resolved = false;
                    const done = () => {
                        if (resolved) return;
                        resolved = true;
                        try { channel.port1.close(); } catch (e) {}
                        try { channel.port2.close(); } catch (e) {}
                        resolve();
                    };
                    channel.port1.onmessage = done;
                    channel.port2.postMessage(0);
                    requestAnimationFrame(() => { setTimeout(done, 0); });
                    return;
                }
                requestAnimationFrame(resolve);
            });
        }

        function loadScriptOnce(src) {
            return new Promise((resolve, reject) => {
                const existing = document.querySelector(`script[data-dynamic-src="${src}"]`);
                if (existing) {
                    existing.addEventListener('load', resolve, { once: true });
                    existing.addEventListener('error', reject, { once: true });
                    if (existing.dataset.loaded === '1') resolve();
                    return;
                }
                const script = document.createElement('script');
                script.src = src;
                script.async = true;
                script.dataset.dynamicSrc = src;
                script.onload = () => {
                    script.dataset.loaded = '1';
                    resolve();
                };
                script.onerror = () => reject(new Error('Unable to load script: ' + src));
                document.head.appendChild(script);
            });
        }

        async function ensureJSZip() {
            if (window.JSZip) return window.JSZip;
            if (!jsZipPromise) {
                jsZipPromise = loadScriptOnce(JSZIP_URL).then(() => {
                    if (!window.JSZip) throw new Error('JSZip is unavailable');
                    return window.JSZip;
                });
            }
            return jsZipPromise;
        }

        function shouldYieldImageProcessing(startTime) {
            return performance.now() - startTime >= 12;
        }

        let imageProcessingKeepAliveDepth = 0;
        let imageProcessingFocusTarget = null;
        let imageProcessingIntervalId = null;
        let imageProcessingWakeLock = null;
        let imageProcessingWakeLockRequest = null;
        let imageProcessingAudioContext = null;
        let imageProcessingAudioOscillator = null;
        let imageProcessingAudioGain = null;
        let imageProcessingLastFocusAt = 0;
        let imageProcessingTouchElement = null;
        let imageProcessingTouchIntervalId = null;
        let imageProcessingTouchRafId = null;
        let imageProcessingTouchPhase = 0;
        let imageProcessingTouchIdentifier = 1;

        function ensureImageProcessingFocusTarget() {
            if (imageProcessingFocusTarget && document.body.contains(imageProcessingFocusTarget)) return imageProcessingFocusTarget;
            imageProcessingFocusTarget = document.createElement('div');
            imageProcessingFocusTarget.setAttribute('tabindex', '-1');
            imageProcessingFocusTarget.setAttribute('aria-hidden', 'true');
            imageProcessingFocusTarget.style.cssText = 'position:fixed;left:0;top:0;width:1px;height:1px;opacity:0;pointer-events:none;z-index:-1;';
            document.body.appendChild(imageProcessingFocusTarget);
            return imageProcessingFocusTarget;
        }

        function focusImageProcessingPage() {
            try {
                if (!document.body || document.visibilityState !== 'visible') return;
                window.focus();
                ensureImageProcessingFocusTarget().focus({ preventScroll: true });
            } catch (error) {
                // 部分移动端浏览器会拒绝脚本聚焦，下面的唤醒锁和静音音频仍会继续尝试保活。
            }
        }

        async function requestImageProcessingWakeLock() {
            if (!imageProcessingKeepAliveDepth || imageProcessingWakeLock || imageProcessingWakeLockRequest || !navigator.wakeLock || document.visibilityState !== 'visible') return;
            try {
                imageProcessingWakeLockRequest = navigator.wakeLock.request('screen');
                const wakeLock = await imageProcessingWakeLockRequest;
                if (!imageProcessingKeepAliveDepth) {
                    wakeLock.release().catch(() => {});
                    return;
                }
                imageProcessingWakeLock = wakeLock;
                imageProcessingWakeLock.addEventListener('release', () => {
                    imageProcessingWakeLock = null;
                });
            } catch (error) {
            } finally {
                imageProcessingWakeLockRequest = null;
            }
        }

        function startImageProcessingSilentAudio() {
            if (imageProcessingAudioContext) return;
            const AudioContextClass = window.AudioContext || window.webkitAudioContext;
            if (!AudioContextClass) return;
            try {
                const audioContext = new AudioContextClass();
                const gain = audioContext.createGain();
                const oscillator = audioContext.createOscillator();
                gain.gain.value = 0.00001;
                oscillator.frequency.value = 20;
                oscillator.connect(gain);
                gain.connect(audioContext.destination);
                oscillator.start();
                if (audioContext.state === 'suspended') {
                    audioContext.resume().catch(() => {});
                }
                imageProcessingAudioContext = audioContext;
                imageProcessingAudioGain = gain;
                imageProcessingAudioOscillator = oscillator;
            } catch (error) {
            }
        }

        function stopImageProcessingSilentAudio() {
            try {
                if (imageProcessingAudioOscillator) imageProcessingAudioOscillator.stop();
            } catch (error) {
                // oscillator 可能已经停止。
            }
            try {
                if (imageProcessingAudioOscillator) imageProcessingAudioOscillator.disconnect();
                if (imageProcessingAudioGain) imageProcessingAudioGain.disconnect();
                if (imageProcessingAudioContext && imageProcessingAudioContext.state !== 'closed') {
                    imageProcessingAudioContext.close();
                }
            } catch (error) {
            }
            imageProcessingAudioContext = null;
            imageProcessingAudioOscillator = null;
            imageProcessingAudioGain = null;
        }

        function createImageProcessingTouchElement() {
            if (imageProcessingTouchElement && document.body.contains(imageProcessingTouchElement)) {
                return imageProcessingTouchElement;
            }
            imageProcessingTouchElement = document.createElement('div');
            imageProcessingTouchElement.style.cssText = 'position:fixed;left:0;top:0;width:100vw;height:100vh;opacity:0;pointer-events:none;z-index:-2;touch-action:none;';
            document.body.appendChild(imageProcessingTouchElement);
            imageProcessingTouchPhase = 0;
            imageProcessingTouchIdentifier = (Date.now() % 9000) + 1000;
            return imageProcessingTouchElement;
        }

        function runImageProcessingTouchSimulation() {
            if (!imageProcessingKeepAliveDepth) return;
            const el = imageProcessingTouchElement;
            if (!el || !document.body.contains(el)) return;
            try {
                const w = window.innerWidth || 375;
                const h = window.innerHeight || 667;
                const steps = 40;
                const cycleLen = steps + 2;
                const phase = imageProcessingTouchPhase % cycleLen;
                const progress = Math.min(1, phase / steps);
                const x = Math.round(20 + (w - 40) * progress);
                const y = Math.round(h * (0.4 + 0.2 * Math.sin(phase * 0.3)));
                const ident = imageProcessingTouchIdentifier;

                if (phase === 0) {
                    const t = new Touch({ identifier: ident, target: el, clientX: x, clientY: y, pageX: x, pageY: y, radiusX: 10, radiusY: 10, force: 0.5 });
                    el.dispatchEvent(new TouchEvent('touchstart', { touches: [t], targetTouches: [t], changedTouches: [t], bubbles: true, cancelable: true }));
                } else if (phase === steps + 1) {
                    const t = new Touch({ identifier: ident, target: el, clientX: x, clientY: y, pageX: x, pageY: y, radiusX: 10, radiusY: 10, force: 0 });
                    el.dispatchEvent(new TouchEvent('touchend', { touches: [], targetTouches: [], changedTouches: [t], bubbles: true, cancelable: true }));
                    imageProcessingTouchIdentifier = ((imageProcessingTouchIdentifier + 1) % 8999) + 1001;
                } else {
                    const t = new Touch({ identifier: ident, target: el, clientX: x, clientY: y, pageX: x, pageY: y, radiusX: 10, radiusY: 10, force: 0.5 });
                    el.dispatchEvent(new TouchEvent('touchmove', { touches: [t], targetTouches: [t], changedTouches: [t], bubbles: true, cancelable: true }));
                }
            } catch (e) {
                // Touch API unavailable on some browsers
            }
            imageProcessingTouchPhase++;
        }

        function startImageProcessingTouchSimulation() {
            createImageProcessingTouchElement();
            imageProcessingTouchPhase = 0;
            imageProcessingTouchIntervalId = window.setInterval(runImageProcessingTouchSimulation, 16);
            function rafLoop() {
                if (!imageProcessingKeepAliveDepth) return;
                runImageProcessingTouchSimulation();
                imageProcessingTouchRafId = requestAnimationFrame(rafLoop);
            }
            imageProcessingTouchRafId = requestAnimationFrame(rafLoop);
        }

        function stopImageProcessingTouchSimulation() {
            if (imageProcessingTouchIntervalId) {
                window.clearInterval(imageProcessingTouchIntervalId);
                imageProcessingTouchIntervalId = null;
            }
            if (imageProcessingTouchRafId) {
                cancelAnimationFrame(imageProcessingTouchRafId);
                imageProcessingTouchRafId = null;
            }
            if (imageProcessingTouchElement && imageProcessingTouchElement.parentNode) {
                imageProcessingTouchElement.remove();
                imageProcessingTouchElement = null;
            }
            imageProcessingTouchPhase = 0;
        }

        function maintainImageProcessingActivity() {
            if (!imageProcessingKeepAliveDepth) return;
            const now = Date.now();
            if (now - imageProcessingLastFocusAt > 8000) {
                imageProcessingLastFocusAt = now;
                focusImageProcessingPage();
            }
            requestImageProcessingWakeLock();
            if (imageProcessingAudioContext && imageProcessingAudioContext.state === 'suspended') {
                imageProcessingAudioContext.resume().catch(() => {});
            }
            if (now - imageProcessingLastFocusAt < 50 && window.mobileWorkKeepAlive && typeof window.mobileWorkKeepAlive.poke === 'function') {
                window.mobileWorkKeepAlive.poke();
            }
        }

        function beginImageProcessingKeepAlive() {
            imageProcessingKeepAliveDepth++;
            if (imageProcessingKeepAliveDepth !== 1) return;
            if (window.mobileWorkKeepAlive) window.mobileWorkKeepAlive.begin();
            startImageProcessingSilentAudio();
            startImageProcessingTouchSimulation();
            imageProcessingLastFocusAt = 0;
            maintainImageProcessingActivity();
            imageProcessingIntervalId = window.setInterval(maintainImageProcessingActivity, 2500);
            document.addEventListener('visibilitychange', maintainImageProcessingActivity);
            window.addEventListener('focus', maintainImageProcessingActivity);
            window.addEventListener('pageshow', maintainImageProcessingActivity);
        }

        function endImageProcessingKeepAlive() {
            imageProcessingKeepAliveDepth = Math.max(0, imageProcessingKeepAliveDepth - 1);
            if (imageProcessingKeepAliveDepth !== 0) return;
            if (imageProcessingIntervalId) {
                window.clearInterval(imageProcessingIntervalId);
                imageProcessingIntervalId = null;
            }
            document.removeEventListener('visibilitychange', maintainImageProcessingActivity);
            window.removeEventListener('focus', maintainImageProcessingActivity);
            window.removeEventListener('pageshow', maintainImageProcessingActivity);
            if (imageProcessingWakeLock) {
                imageProcessingWakeLock.release().catch(error => {
                });
                imageProcessingWakeLock = null;
            }
            imageProcessingWakeLockRequest = null;
            stopImageProcessingSilentAudio();
            stopImageProcessingTouchSimulation();
            if (window.mobileWorkKeepAlive) window.mobileWorkKeepAlive.end();
        }

        // XOR 密钥计算函数
        function getFixedXORKey(password) {
            return XOR_FIXED_KEY;
        }

        // XOR 加密/解密函数（同步，不yield——手机端浏览器会节流延时函数导致极慢）
        function applyXOR(data, key) {
            for (let i = 0; i < data.length; i += 4) {
                data[i] = data[i] ^ key;
                data[i + 1] = data[i + 1] ^ key;
                data[i + 2] = data[i + 2] ^ key;
            }
            return data;
        }

        async function remapImagePixelsAsync(data, pixelMap, totalPixels) {
            const newData = new Uint8ClampedArray(data.length);
            let startTime = performance.now();
            for (let dstIdx = 0; dstIdx < totalPixels; dstIdx++) {
                const srcIdx = pixelMap[dstIdx];
                const dstOffset = dstIdx * 4;
                const srcOffset = srcIdx * 4;
                newData[dstOffset] = data[srcOffset];
                newData[dstOffset + 1] = data[srcOffset + 1];
                newData[dstOffset + 2] = data[srcOffset + 2];
                newData[dstOffset + 3] = data[srcOffset + 3];
                if ((dstIdx % IMAGE_PROCESSING_CHUNK_PIXELS) === 0 && shouldYieldImageProcessing(startTime)) {
                    await yieldToBrowser();
                    startTime = performance.now();
                }
            }
            return newData;
        }

        // 更新加密计数显示
        function getImageRemapWorker() {
            if (!imageRemapWorkerAvailable) return null;
            if (imageRemapWorker) return imageRemapWorker;
            try {
                const workerSource = `
                    self.onmessage = function(event) {
                        var message = event.data || {};
                        if (message.type !== 'remap') return;
                        try {
                            var data = new Uint8ClampedArray(message.dataBuffer);
                            var map = new Uint32Array(message.mapBuffer);
                            var totalPixels = message.totalPixels;
                            var output = new Uint8ClampedArray(data.length);
                            for (var dstIdx = 0; dstIdx < totalPixels; dstIdx++) {
                                var srcIdx = map[dstIdx];
                                var dstOffset = dstIdx * 4;
                                var srcOffset = srcIdx * 4;
                                output[dstOffset] = data[srcOffset];
                                output[dstOffset + 1] = data[srcOffset + 1];
                                output[dstOffset + 2] = data[srcOffset + 2];
                                output[dstOffset + 3] = data[srcOffset + 3];
                            }
                            self.postMessage({ id: message.id, ok: true, buffer: output.buffer }, [output.buffer]);
                        } catch (error) {
                            self.postMessage({ id: message.id, ok: false, error: error && error.message ? error.message : String(error) });
                        }
                    };
                `;
                imageRemapWorkerUrl = URL.createObjectURL(new Blob([workerSource], { type: 'application/javascript' }));
                imageRemapWorker = new Worker(imageRemapWorkerUrl);
                imageRemapWorker.onmessage = function(event) {
                    const message = event.data || {};
                    const job = imageRemapWorkerJobs.get(message.id);
                    if (!job) return;
                    imageRemapWorkerJobs.delete(message.id);
                    if (message.ok) job.resolve(new Uint8ClampedArray(message.buffer));
                    else job.reject(new Error(message.error || 'Image remap worker failed'));
                };
                imageRemapWorker.onerror = function(error) {
                    const pendingJobs = Array.from(imageRemapWorkerJobs.values());
                    imageRemapWorkerJobs.clear();
                    imageRemapWorkerAvailable = false;
                    imageRemapWorker = null;
                    pendingJobs.forEach(job => job.reject(new Error(error && error.message ? error.message : 'Image remap worker failed')));
                };
                return imageRemapWorker;
            } catch (error) {
                imageRemapWorkerAvailable = false;
                if (imageRemapWorkerUrl) {
                    URL.revokeObjectURL(imageRemapWorkerUrl);
                    imageRemapWorkerUrl = null;
                }
                return null;
            }
        }

        function remapImagePixelsInWorker(data, pixelMap, totalPixels) {
            const worker = getImageRemapWorker();
            if (!worker) return null;
            const jobId = ++imageRemapWorkerJobId;
            return new Promise((resolve, reject) => {
                imageRemapWorkerJobs.set(jobId, { resolve, reject });
                try {
                    worker.postMessage({
                        type: 'remap',
                        id: jobId,
                        dataBuffer: data.buffer,
                        mapBuffer: pixelMap.buffer,
                        totalPixels
                    });
                } catch (error) {
                    imageRemapWorkerJobs.delete(jobId);
                    reject(error);
                }
            });
        }

        function createImageGpuShader(gl, type, source) {
            const shader = gl.createShader(type);
            gl.shaderSource(shader, source);
            gl.compileShader(shader);
            if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
                const message = gl.getShaderInfoLog(shader) || 'Unknown shader compile error';
                gl.deleteShader(shader);
                throw new Error(message);
            }
            return shader;
        }

        function createImageGpuProgram(gl) {
            const vertexShader = createImageGpuShader(gl, gl.VERTEX_SHADER, `
                attribute vec2 a_position;
                void main() {
                    gl_Position = vec4(a_position, 0.0, 1.0);
                }
            `);
            const fragmentShader = createImageGpuShader(gl, gl.FRAGMENT_SHADER, `
                precision highp float;
                uniform sampler2D u_image;
                uniform sampler2D u_map;
                uniform vec2 u_size;
                void main() {
                    float dstX = floor(gl_FragCoord.x);
                    float dstY = floor(gl_FragCoord.y);
                    vec2 dstUv = vec2((dstX + 0.5) / u_size.x, 1.0 - ((dstY + 0.5) / u_size.y));
                    vec4 mapColor = texture2D(u_map, dstUv);
                    float srcIndex = floor(mapColor.r * 255.0 + 0.5)
                        + floor(mapColor.g * 255.0 + 0.5) * 256.0
                        + floor(mapColor.b * 255.0 + 0.5) * 65536.0;
                    float srcY = floor(srcIndex / u_size.x);
                    float srcX = srcIndex - srcY * u_size.x;
                    vec2 srcUv = vec2((srcX + 0.5) / u_size.x, 1.0 - ((srcY + 0.5) / u_size.y));
                    gl_FragColor = texture2D(u_image, srcUv);
                }
            `);
            const program = gl.createProgram();
            gl.attachShader(program, vertexShader);
            gl.attachShader(program, fragmentShader);
            gl.linkProgram(program);
            gl.deleteShader(vertexShader);
            gl.deleteShader(fragmentShader);
            if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
                const message = gl.getProgramInfoLog(program) || 'Unknown program link error';
                gl.deleteProgram(program);
                throw new Error(message);
            }
            return program;
        }

        function createImageGpuTexture(gl, unit, width, height, data) {
            const texture = gl.createTexture();
            gl.activeTexture(gl.TEXTURE0 + unit);
            gl.bindTexture(gl.TEXTURE_2D, texture);
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
            gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true);
            gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, width, height, 0, gl.RGBA, gl.UNSIGNED_BYTE, data);
            gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, false);
            return texture;
        }

        function packPixelMapForGpu(pixelMap, totalPixels) {
            const packed = new Uint8Array(totalPixels * 4);
            for (let i = 0; i < totalPixels; i++) {
                const srcIdx = pixelMap[i];
                const offset = i * 4;
                packed[offset] = srcIdx & 255;
                packed[offset + 1] = (srcIdx >> 8) & 255;
                packed[offset + 2] = (srcIdx >> 16) & 255;
                packed[offset + 3] = 255;
            }
            return packed;
        }

        function remapImagePixelsGpu(data, pixelMap, width, height) {
            const totalPixels = width * height;
            if (totalPixels > GPU_REMAP_MAX_PACKED_INDEX) throw new Error('Image is too large for packed WebGL remap');
            const canvas = document.createElement('canvas');
            canvas.width = width;
            canvas.height = height;
            const gl = canvas.getContext('webgl', { alpha: true, antialias: false, depth: false, stencil: false, preserveDrawingBuffer: true });
            if (!gl) throw new Error('WebGL is unavailable');
            const maxTextureSize = gl.getParameter(gl.MAX_TEXTURE_SIZE);
            if (width > maxTextureSize || height > maxTextureSize) throw new Error('Image exceeds max WebGL texture size');

            const program = createImageGpuProgram(gl);
            const positionBuffer = gl.createBuffer();
            gl.bindBuffer(gl.ARRAY_BUFFER, positionBuffer);
            gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([-1,-1, 1,-1, -1,1, -1,1, 1,-1, 1,1]), gl.STATIC_DRAW);
            const imageTexture = createImageGpuTexture(gl, 0, width, height, data);
            const mapTexture = createImageGpuTexture(gl, 1, width, height, packPixelMapForGpu(pixelMap, totalPixels));
            const output = new Uint8Array(data.length);

            gl.viewport(0, 0, width, height);
            gl.useProgram(program);
            const positionLocation = gl.getAttribLocation(program, 'a_position');
            gl.enableVertexAttribArray(positionLocation);
            gl.vertexAttribPointer(positionLocation, 2, gl.FLOAT, false, 0, 0);
            gl.uniform1i(gl.getUniformLocation(program, 'u_image'), 0);
            gl.uniform1i(gl.getUniformLocation(program, 'u_map'), 1);
            gl.uniform2f(gl.getUniformLocation(program, 'u_size'), width, height);
            gl.drawArrays(gl.TRIANGLES, 0, 6);
            gl.readPixels(0, 0, width, height, gl.RGBA, gl.UNSIGNED_BYTE, output);

            gl.deleteTexture(imageTexture);
            gl.deleteTexture(mapTexture);
            gl.deleteBuffer(positionBuffer);
            gl.deleteProgram(program);
            return new Uint8ClampedArray(output.buffer);
        }

        async function remapImagePixelsWithGpuFallback(data, pixelMap, width, height) {
            const totalPixels = width * height;
            if (totalPixels >= GPU_REMAP_MIN_PIXELS && totalPixels <= GPU_REMAP_MAX_PACKED_INDEX && imageGpuRemapAvailable !== false) {
                try {
                    const result = remapImagePixelsGpu(data, pixelMap, width, height);
                    imageGpuRemapAvailable = true;
                    await yieldToBrowser();
                    return result;
                } catch (error) {
                    imageGpuRemapAvailable = false;
                }
            }
            if (totalPixels >= WORKER_REMAP_MIN_PIXELS && imageRemapWorkerAvailable) {
                const workerResultPromise = remapImagePixelsInWorker(data, pixelMap, totalPixels);
                if (workerResultPromise) {
                    try {
                        const result = await workerResultPromise;
                        await yieldToBrowser();
                        return result;
                    } catch (error) {
                    }
                }
            }
            return remapImagePixelsAsync(data, pixelMap, totalPixels);
        }

        function updateEncryptCounter() {
            const counter = document.getElementById('encryptCounter');
            if (counter) {
                counter.textContent = encryptCount;
            }
        }

        function refreshImageCompatNote() {
            if (!imageCompatNote) return;
            const messages = [];
            if (!imageRuntime.hasOffscreenCanvas || !imageRuntime.hasCreateImageBitmap) {
                messages.push('当前浏览器已启用兼容模式处理图片。');
            }
            if (imageRuntime.webpTranscodeSupported === false) {
                messages.push('色彩反转和 WEBP 导出已关闭，其它加密/解密仍可正常使用。');
            }
            imageCompatNote.textContent = messages.join(' ');
            imageCompatNote.style.display = messages.length ? 'block' : 'none';
        }

        function getImageExportOptions(format) {
            if (format === 'jpg95') return { type: 'image/jpeg', quality: 0.95 };
            if (format === 'webp') return { type: 'image/webp', quality: 1.0 };
            return { type: 'image/png', quality: undefined };
        }

        function createCanvasSurface(width, height) {
            if (!width || !height || width <= 0 || height <= 0) {
                throw new Error('Invalid image dimensions: ' + width + 'x' + height);
            }
            const canvas = imageRuntime.hasOffscreenCanvas ? new OffscreenCanvas(width, height) : document.createElement('canvas');
            canvas.width = width;
            canvas.height = height;
            const ctx = canvas.getContext('2d', { willReadFrequently: true });
            if (!ctx) {
                throw new Error('2D canvas is not supported in this browser');
            }
            return { canvas, ctx };
        }

        function dataUrlToBlob(dataUrl) {
            const parts = dataUrl.split(',');
            if (parts.length < 2) {
                throw new Error('Canvas export failed');
            }
            const mimeMatch = parts[0].match(/data:([^;]+)(;base64)?/i);
            const mime = mimeMatch ? mimeMatch[1] : 'application/octet-stream';
            const binary = atob(parts[1]);
            const bytes = new Uint8Array(binary.length);
            for (let i = 0; i < binary.length; i++) {
                bytes[i] = binary.charCodeAt(i);
            }
            return new Blob([bytes], { type: mime });
        }

        async function canvasToBlobCompat(canvas, options) {
            const type = options && options.type ? options.type : 'image/png';
            const quality = options ? options.quality : undefined;
            if (typeof canvas.convertToBlob === 'function') {
                return canvas.convertToBlob({ type, quality });
            }
            if (typeof canvas.toBlob === 'function') {
                return new Promise((resolve, reject) => {
                    canvas.toBlob((blob) => {
                        if (blob) resolve(blob);
                        else reject(new Error('Canvas export failed'));
                    }, type, quality);
                });
            }
            if (typeof canvas.toDataURL === 'function') {
                return dataUrlToBlob(canvas.toDataURL(type, quality));
            }
            throw new Error('Canvas export is not supported in this browser');
        }

        async function loadImageSource(fileOrBlob) {
            if (imageRuntime.hasCreateImageBitmap) {
                try {
                    const bitmap = await createImageBitmap(fileOrBlob);
                    return {
                        source: bitmap,
                        width: bitmap.width,
                        height: bitmap.height,
                        cleanup() {
                            if (typeof bitmap.close === 'function') bitmap.close();
                        }
                    };
                } catch (error) {
                }
            }
            const url = URL.createObjectURL(fileOrBlob);
            return new Promise((resolve, reject) => {
                const img = new Image();
                img.decoding = 'async';
                img.onload = () => {
                    resolve({
                        source: img,
                        width: img.naturalWidth || img.width,
                        height: img.naturalHeight || img.height,
                        cleanup() {
                            URL.revokeObjectURL(url);
                        }
                    });
                };
                img.onerror = () => {
                    URL.revokeObjectURL(url);
                    reject(new Error('Unable to decode image'));
                };
                img.src = url;
            });
        }

        function readBlobArrayBuffer(blob) {
            if (blob && typeof blob.arrayBuffer === 'function') return blob.arrayBuffer();
            return new Promise((resolve, reject) => {
                const reader = new FileReader();
                reader.onload = () => resolve(reader.result);
                reader.onerror = () => reject(reader.error || new Error('Unable to read file header'));
                reader.readAsArrayBuffer(blob);
            });
        }

        function asciiFromBytes(view, offset, length) {
            if (offset + length > view.byteLength) return '';
            let value = '';
            for (let i = 0; i < length; i++) value += String.fromCharCode(view.getUint8(offset + i));
            return value;
        }

        function normalizeImageDimensions(width, height) {
            const absoluteHeight = Math.abs(height);
            if (!Number.isFinite(width) || !Number.isFinite(height) || width <= 0 || absoluteHeight <= 0) return null;
            return { width: Math.round(width), height: Math.round(absoluteHeight) };
        }

        function isJpegSofMarker(marker) {
            return (marker >= 0xC0 && marker <= 0xCF && ![0xC4, 0xC8, 0xCC].includes(marker));
        }

        function parseJpegDimensions(view) {
            if (view.byteLength < 4 || view.getUint8(0) !== 0xFF || view.getUint8(1) !== 0xD8) return null;
            let offset = 2;
            while (offset < view.byteLength) {
                if (view.getUint8(offset) !== 0xFF) {
                    offset++;
                    continue;
                }
                while (offset < view.byteLength && view.getUint8(offset) === 0xFF) offset++;
                if (offset >= view.byteLength) break;
                const marker = view.getUint8(offset++);
                if (marker === 0xD8 || marker === 0x01) continue;
                if (marker === 0xD9 || marker === 0xDA) break;
                if (offset + 2 > view.byteLength) break;
                const segmentLength = view.getUint16(offset, false);
                if (segmentLength < 2) break;
                const segmentStart = offset + 2;
                if (isJpegSofMarker(marker)) {
                    if (segmentStart + 5 > view.byteLength) break;
                    return normalizeImageDimensions(
                        view.getUint16(segmentStart + 3, false),
                        view.getUint16(segmentStart + 1, false)
                    );
                }
                offset += segmentLength;
            }
            return null;
        }

        function readUint24LE(view, offset) {
            if (offset + 3 > view.byteLength) return 0;
            return view.getUint8(offset) | (view.getUint8(offset + 1) << 8) | (view.getUint8(offset + 2) << 16);
        }

        function parseWebpDimensions(view) {
            if (view.byteLength < 30 || asciiFromBytes(view, 0, 4) !== 'RIFF' || asciiFromBytes(view, 8, 4) !== 'WEBP') return null;
            let offset = 12;
            while (offset + 8 <= view.byteLength) {
                const chunkType = asciiFromBytes(view, offset, 4);
                const chunkSize = view.getUint32(offset + 4, true);
                const dataOffset = offset + 8;
                if (chunkType === 'VP8X' && dataOffset + 10 <= view.byteLength) {
                    return normalizeImageDimensions(
                        readUint24LE(view, dataOffset + 4) + 1,
                        readUint24LE(view, dataOffset + 7) + 1
                    );
                }
                if (chunkType === 'VP8 ' && dataOffset + 10 <= view.byteLength) {
                    return normalizeImageDimensions(
                        view.getUint16(dataOffset + 6, true) & 0x3FFF,
                        view.getUint16(dataOffset + 8, true) & 0x3FFF
                    );
                }
                if (chunkType === 'VP8L' && dataOffset + 5 <= view.byteLength && view.getUint8(dataOffset) === 0x2F) {
                    const b0 = view.getUint8(dataOffset + 1);
                    const b1 = view.getUint8(dataOffset + 2);
                    const b2 = view.getUint8(dataOffset + 3);
                    const b3 = view.getUint8(dataOffset + 4);
                    return normalizeImageDimensions(
                        1 + (((b1 & 0x3F) << 8) | b0),
                        1 + (((b3 & 0x0F) << 10) | (b2 << 2) | ((b1 & 0xC0) >> 6))
                    );
                }
                offset = dataOffset + chunkSize + (chunkSize % 2);
            }
            return null;
        }

        function parseImageDimensionsFromHeader(view) {
            if (view.byteLength >= 24 &&
                view.getUint8(0) === 0x89 &&
                asciiFromBytes(view, 1, 3) === 'PNG') {
                return normalizeImageDimensions(view.getUint32(16, false), view.getUint32(20, false));
            }
            const jpeg = parseJpegDimensions(view);
            if (jpeg) return jpeg;
            if (view.byteLength >= 10) {
                const gifHeader = asciiFromBytes(view, 0, 6);
                if (gifHeader === 'GIF87a' || gifHeader === 'GIF89a') {
                    return normalizeImageDimensions(view.getUint16(6, true), view.getUint16(8, true));
                }
            }
            if (view.byteLength >= 26 && asciiFromBytes(view, 0, 2) === 'BM') {
                return normalizeImageDimensions(view.getInt32(18, true), view.getInt32(22, true));
            }
            return parseWebpDimensions(view);
        }

        function isLikelyJpegHeader(view) {
            return view.byteLength >= 2 && view.getUint8(0) === 0xFF && view.getUint8(1) === 0xD8;
        }

        async function readImageDimensionsFast(file) {
            try {
                const quickLength = Math.min(file.size || QUICK_IMAGE_DIMENSION_HEADER_BYTES, QUICK_IMAGE_DIMENSION_HEADER_BYTES);
                const quickBuffer = await readBlobArrayBuffer(file.slice(0, quickLength));
                const quickView = new DataView(quickBuffer);
                const quickDimensions = parseImageDimensionsFromHeader(quickView);
                if (quickDimensions) return quickDimensions;

                const extendedLength = Math.min(file.size || LARGE_IMAGE_DIMENSION_HEADER_BYTES, LARGE_IMAGE_DIMENSION_HEADER_BYTES);
                if (!isLikelyJpegHeader(quickView) || extendedLength <= quickLength) return null;

                const extendedBuffer = await readBlobArrayBuffer(file.slice(0, extendedLength));
                return parseImageDimensionsFromHeader(new DataView(extendedBuffer));
            } catch (error) {
                return null;
            }
        }

        function buildImageInfo(file, index, dimensions) {
            const pixels = dimensions.width * dimensions.height;
            return {
                index,
                name: file.name || 'image',
                size: file.size || 0,
                width: dimensions.width,
                height: dimensions.height,
                pixels,
                isLarge: pixels > LARGE_IMAGE_PIXEL_LIMIT
            };
        }

        async function inspectImageByDecode(file, index) {
            const imageSource = await loadImageSource(file);
            try {
                return buildImageInfo(file, index, {
                    width: imageSource.width,
                    height: imageSource.height
                });
            } finally {
                imageSource.cleanup();
            }
        }

        async function inspectImageHeaders(files) {
            const infos = new Array(files.length);
            const fallbackIndexes = [];
            await Promise.all(files.map(async (file, index) => {
                const dimensions = await readImageDimensionsFast(file);
                if (dimensions) {
                    infos[index] = buildImageInfo(file, index, dimensions);
                } else {
                    fallbackIndexes.push(index);
                }
            }));
            return { infos, fallbackIndexes: fallbackIndexes.sort((a, b) => a - b) };
        }

        async function inspectImageFallbacks(files, fallbackIndexes, infos) {
            for (const index of fallbackIndexes) {
                const file = files[index];
                try {
                    infos[index] = await inspectImageByDecode(file, index);
                } catch (error) {
                }
            }
            return infos.filter(Boolean);
        }

        async function inspectLargeImages(files) {
            const { infos, fallbackIndexes } = await inspectImageHeaders(files);
            return inspectImageFallbacks(files, fallbackIndexes, infos);
        }

        let largeImageOverlayLockCount = 0;
        let largeImageOverlayPreviousOverflow = '';
        let largeImageOverlayPreviousTouchAction = '';

        function lockLargeImageBackgroundScroll() {
            if (largeImageOverlayLockCount === 0) {
                largeImageOverlayPreviousOverflow = document.body.style.overflow;
                largeImageOverlayPreviousTouchAction = document.body.style.touchAction;
                document.body.style.overflow = 'hidden';
                document.body.style.touchAction = 'none';
            }
            largeImageOverlayLockCount++;
        }

        function unlockLargeImageBackgroundScroll() {
            largeImageOverlayLockCount = Math.max(0, largeImageOverlayLockCount - 1);
            if (largeImageOverlayLockCount === 0) {
                document.body.style.overflow = largeImageOverlayPreviousOverflow;
                document.body.style.touchAction = largeImageOverlayPreviousTouchAction;
            }
        }

        function removeLargeImageElement(element) {
            if (!element || !element.parentNode) return;
            element.classList.add('closing');
            window.setTimeout(() => {
                if (element.parentNode) element.remove();
                unlockLargeImageBackgroundScroll();
            }, 170);
        }

        function buildLargeImageWarningMessage(largeInfos) {
            const maxInfo = largeInfos.reduce((max, info) => info.pixels > max.pixels ? info : max, largeInfos[0]);
            const summary = largeInfos.length === 1
                ? '检测到大图：' + maxInfo.width + '×' + maxInfo.height
                : '检测到 ' + largeInfos.length + ' 张大图，最大：' + maxInfo.width + '×' + maxInfo.height;
            const allInfos = largeImageInfos.length ? largeImageInfos : largeInfos;
            const visibleInfos = allInfos.slice(0, 12);
            const detailText = visibleInfos
                .map(info => (info.index + 1) + '. ' + info.width + '×' + info.height + '  ' + info.name)
                .join('\n');
            const moreText = allInfos.length > visibleInfos.length ? '\n...还有 ' + (allInfos.length - visibleInfos.length) + ' 张' : '';
            return detailText ? summary + '\n' + detailText + moreText : summary;
        }

        function getLargeImageImportTitle(largeInfos) {
            if (selectedImageFiles.length === 1) {
                return '你导入的图片太大了';
            }
            if (largeInfos.length === selectedImageFiles.length) {
                return '你导入的图片全部太大了';
            }
            return '你导入的图片有些太大了';
        }

        function getLargeImageCompressedSize(width, height) {
            const pixels = width * height;
            if (pixels <= LARGE_IMAGE_PIXEL_LIMIT) {
                return { width, height, changed: false };
            }
            const scale = Math.sqrt(LARGE_IMAGE_PIXEL_LIMIT / pixels);
            return {
                width: Math.max(1, Math.round(width * scale)),
                height: Math.max(1, Math.round(height * scale)),
                changed: true
            };
        }

        async function compressLargeImportedImages(largeInfos) {
            const largeIndexSet = new Set(largeInfos.map(info => info.index));
            const compressedFiles = [];
            for (let index = 0; index < selectedImageFiles.length; index++) {
                const file = selectedImageFiles[index];
                if (!largeIndexSet.has(index)) {
                    compressedFiles[index] = file;
                    continue;
                }
                const imageSource = await loadImageSource(file);
                const target = getLargeImageCompressedSize(imageSource.width, imageSource.height);
                const { canvas, ctx } = createCanvasSurface(target.width, target.height);
                ctx.imageSmoothingEnabled = true;
                ctx.imageSmoothingQuality = 'high';
                ctx.drawImage(imageSource.source, 0, 0, target.width, target.height);
                imageSource.cleanup();
                const sourceType = file.type && /^image\/(png|jpeg|webp)$/i.test(file.type) ? file.type : 'image/png';
                const blob = await canvasToBlobCompat(canvas, { type: sourceType, quality: sourceType === 'image/png' ? undefined : 0.95 });
                compressedFiles[index] = createFileLike(blob, file.name || `compressed_${index}.png`);
            }
            selectedImageFiles = compressedFiles;
            previewUrls.forEach(url => URL.revokeObjectURL(url));
            previewUrls = selectedImageFiles.map(f => URL.createObjectURL(f));
            latestProcessedImages = [];
            latestKeyParams = null;
            clearTransientImageCache();
            largeImageInfos = await inspectLargeImages(selectedImageFiles);
            selectedCountDisplay.value = '已压缩' + largeInfos.length + '张大图';
        }

        function showLargeImageCompressLoader(largeInfos, workPromiseFactory) {
            if (!largeInfos.length) return Promise.resolve();
            const maxInfo = largeInfos.reduce((max, info) => info.pixels > max.pixels ? info : max, largeInfos[0]);
            const target = getLargeImageCompressedSize(maxInfo.width, maxInfo.height);
            const detailText = largeInfos.length === 1
                ? '分辨率：' + maxInfo.width + '×' + maxInfo.height + ' → ' + target.width + '×' + target.height
                : '共 ' + largeInfos.length + ' 张大图，最大图：' + maxInfo.width + '×' + maxInfo.height + ' → ' + target.width + '×' + target.height;
            const loader = document.createElement('div');
            loader.className = 'large-image-compress-loader';
            loader.innerHTML = `
                <div class="large-image-compress-card">
                    <div class="large-image-compress-title">正在压缩图片</div>
                    <div class="large-image-compress-subtitle">正在按比例缩小分辨率，避免图片过大。</div>
                    <div class="large-image-compress-visual">
                        <div class="large-image-compress-box"></div>
                        <div class="large-image-compress-arrow">→</div>
                        <div class="large-image-compress-box after"></div>
                    </div>
                    <div class="large-image-compress-progress"><span></span></div>
                    <div class="large-image-compress-detail">${detailText}</div>
                </div>
            `;
            document.body.appendChild(loader);
            lockLargeImageBackgroundScroll();
            loader.style.display = 'flex';
            const startedAt = Date.now();
            const work = Promise.resolve().then(() => {
                if (typeof workPromiseFactory === 'function') {
                    return workPromiseFactory();
                }
            });
            return work.then(() => {
                const remainingDelay = Math.max(0, 1050 - (Date.now() - startedAt));
                if (remainingDelay > 0) {
                    return new Promise(resolve => window.setTimeout(resolve, remainingDelay));
                }
            }).finally(() => {
                removeLargeImageElement(loader);
            });
        }

        function showLargeImageImportWarning(largeInfos) {
            if (!largeInfos.length) return;
            const message = buildLargeImageWarningMessage(largeInfos);
            const title = getLargeImageImportTitle(largeInfos);
            const modal = document.createElement('div');
            modal.className = 'large-image-warning-modal';
            modal.innerHTML = `
                <div class="large-image-warning-window">
                    <h3>${title}</h3>
                    <p class="large-image-warning-summary"></p>
                    <p class="large-image-warning-lead">如果要发到平台，建议先压缩。</p>
                    <div class="large-image-warning-list">
                        <div class="large-image-warning-item">
                            <strong>我要压缩</strong>
                            <span>适合制作混淆图后发布，降低被平台再次压缩的风险。</span>
                        </div>
                        <div class="large-image-warning-item">
                            <strong>不要压缩</strong>
                            <span>适合发网盘、自己保存，或者解密别人发来的混淆图。</span>
                        </div>
                    </div>
                    <label class="large-image-warning-check">
                        <input type="checkbox" class="large-image-warning-never">
                        <span>以后不再提醒</span>
                    </label>
                    <div class="large-image-warning-actions">
                        <button type="button" class="large-image-warning-choice" data-choice="keep">不要压缩</button>
                        <button type="button" class="large-image-warning-choice primary" data-choice="compress">我要压缩</button>
                    </div>
                </div>
            `;
            modal.querySelector('.large-image-warning-summary').textContent = message;
            document.body.appendChild(modal);
            lockLargeImageBackgroundScroll();
            modal.style.display = 'flex';
            let isClosing = false;
            const close = async (choice) => {
                if (isClosing) return;
                isClosing = true;
                latestLargeImageImportChoice = choice || 'keep';
                const never = modal.querySelector('.large-image-warning-never');
                if (never && never.checked) {
                    isLargeImageWarningEnabled = false;
                    localStorage.setItem(LARGE_IMAGE_WARNING_STORAGE_KEY, '0');
                    if (largeImageWarningToggle) largeImageWarningToggle.checked = false;
                }
                if (latestLargeImageImportChoice === 'compress') {
                    removeLargeImageElement(modal);
                    await showLargeImageCompressLoader(largeInfos, () => compressLargeImportedImages(largeInfos));
                    await updateFirstImageCache();
                    if (imgMethod === 'block' && encryptMethodModal.style.display === 'flex') updateBlockSizeOptions();
                } else {
                    removeLargeImageElement(modal);
                    schedulePostImportDimensionWork();
                }
            };
            modal.querySelectorAll('.large-image-warning-choice').forEach(button => {
                button.addEventListener('click', () => close(button.dataset.choice));
            });
            modal.addEventListener('click', (event) => {
                if (event.target === modal) close('keep');
            });
        }

        function showLargeImageWarningHelp() {
            const modal = document.createElement('div');
            modal.className = 'large-image-warning-modal';
            modal.innerHTML = `
                <div class="large-image-warning-window">
                    <h3>导入大图提醒</h3>
                    <p class="large-image-warning-lead">图片太大时，导入后会提醒你先看一眼。</p>
                    <div class="large-image-warning-list">
                        <div class="large-image-warning-item">
                            <strong>要发到平台</strong>
                            <span>建议先压缩，避免平台再压一次，影响别人还原。</span>
                        </div>
                        <div class="large-image-warning-item">
                            <strong>发网盘 / 自己保存 / 解密图片</strong>
                            <span>一般不用管，保持原图就行。</span>
                        </div>
                    </div>
                    <p class="large-image-warning-muted">这个开关只控制导入时是否提醒，不会自动压缩图片。</p>
                    <div class="large-image-warning-actions">
                        <button type="button" class="large-image-warning-ok">知道了</button>
                    </div>
                </div>
            `;
            document.body.appendChild(modal);
            lockLargeImageBackgroundScroll();
            modal.style.display = 'flex';
            const close = () => removeLargeImageElement(modal);
            modal.querySelector('.large-image-warning-ok').addEventListener('click', close);
            modal.addEventListener('click', (event) => {
                if (event.target === modal) close();
            });
        }

        function createFileLike(blob, name) {
            if (typeof File === 'function') {
                return new File([blob], name, { type: blob.type });
            }
            const fileLike = blob.slice(0, blob.size, blob.type);
            fileLike.name = name;
            return fileLike;
        }

        function updateWebpAvailability(isSupported) {
            imageRuntime.webpTranscodeSupported = isSupported;
            xorToggle.disabled = !isSupported;
            if (!isSupported) {
                xorToggle.checked = false;
                isXOREnabled = false;
                localStorage.setItem(XOR_ENABLED_STORAGE_KEY, '0');
            }
            const webpOption = imgFormatSelect.querySelector('option[value="webp"]');
            if (webpOption) {
                webpOption.disabled = !isSupported;
            }
            if (!isSupported && imgFormatSelect.value === 'webp') {
                imgFormatSelect.value = 'png';
            }
            if (batchFormatSelect) {
                const batchWebpOption = batchFormatSelect.querySelector('option[value="webp"]');
                if (batchWebpOption) {
                    batchWebpOption.disabled = !isSupported;
                }
                if (!isSupported && batchFormatSelect.value === 'webp') {
                    batchFormatSelect.value = 'png';
                }
            }
            refreshImageCompatNote();
        }

        async function testWebpTranscodeSupport() {
            try {
                const surface = createCanvasSurface(2, 2);
                surface.ctx.fillStyle = '#000';
                surface.ctx.fillRect(0, 0, 2, 2);
                const blob = await canvasToBlobCompat(surface.canvas, { type: 'image/webp', quality: 1.0 });
                if (!blob || blob.size === 0 || !/^image\/webp$/i.test(blob.type || '')) {
                    return false;
                }
                const decoded = await loadImageSource(blob);
                try {
                    return decoded.width > 0 && decoded.height > 0;
                } finally {
                    decoded.cleanup();
                }
            } catch (error) {
                return false;
            }
        }

        async function applyImageCompatibility() {
            refreshImageCompatNote();
            const webpSupported = await testWebpTranscodeSupport();
            updateWebpAvailability(webpSupported);
        }

        // 重加密功能切换
        reencryptToggleBtn.addEventListener('click', function() {
            isReencryptEnabled = !isReencryptEnabled;
            if (isReencryptEnabled) {
                reencryptToggleBtn.innerHTML = '✅ 允许重加密';
                reencryptToggleBtn.classList.remove('disabled');
                reencryptToggleBtn.classList.add('highlight');
                // 开启允许重加密时，启用加密和解密按钮
                enableExportControls();
            } else {
                reencryptToggleBtn.innerHTML = '🚫 禁止重加密';
                reencryptToggleBtn.classList.remove('highlight');
                reencryptToggleBtn.classList.add('disabled');
            }
        });

        // 辅助哈希
        function simpleHash(s) { let h=0; for(let i=0;i<s.length;i++){ h=((h<<5)-h)+s.charCodeAt(i); h|=0; } return Math.abs(h); }

        // 吉尔伯特曲线 (返回坐标数组)
        function gilbert2d(width, height) {
            const coordinates = new Uint32Array(width * height);
            const state = { index: 0 };
            if (width >= height) generate2d(0, 0, width, 0, 0, height, width, coordinates, state);
            else generate2d(0, 0, 0, height, width, 0, width, coordinates, state);
            return coordinates;
        }
        function generate2d(x, y, ax, ay, bx, by, width, coordinates, state) {
            const w = Math.abs(ax + ay), h = Math.abs(bx + by);
            const dax = Math.sign(ax), day = Math.sign(ay), dbx = Math.sign(bx), dby = Math.sign(by);
            if (h === 1) { for (let i = 0; i < w; i++) { coordinates[state.index++] = y * width + x; x += dax; y += day; } return; }
            if (w === 1) { for (let i = 0; i < h; i++) { coordinates[state.index++] = y * width + x; x += dbx; y += dby; } return; }
            let ax2 = Math.floor(ax / 2), ay2 = Math.floor(ay / 2), bx2 = Math.floor(bx / 2), by2 = Math.floor(by / 2);
            const w2 = Math.abs(ax2 + ay2), h2 = Math.abs(bx2 + by2);
            if (2 * w > 3 * h) {
                if ((w2 % 2) && (w > 2)) { ax2 += dax; ay2 += day; }
                generate2d(x, y, ax2, ay2, bx, by, width, coordinates, state);
                generate2d(x + ax2, y + ay2, ax - ax2, ay - ay2, bx, by, width, coordinates, state);
            } else {
                if ((h2 % 2) && (h > 2)) { bx2 += dbx; by2 += dby; }
                generate2d(x, y, bx2, by2, ax2, ay2, width, coordinates, state);
                generate2d(x + bx2, y + by2, ax, ay, bx - bx2, by - by2, width, coordinates, state);
                generate2d(x + (ax - dax) + (bx2 - dbx), y + (ay - day) + (by2 - dby), -bx2, -by2, -(ax - ax2), -(ay - ay2), width, coordinates, state);
            }
        }

        function buildGilbertEncryptMap(width, height, key) {
            const total = width * height;
            const curveCoords = gilbert2d(width, height);
            let offset = key ? simpleHash(key) % total : Math.round((Math.sqrt(5)-1)/2 * total);
            const encMap = new Uint32Array(total);
            for (let i = 0; i < total; i++) {
                const oldLinear = curveCoords[i];
                const newLinear = curveCoords[(i + offset) % total];
                encMap[newLinear] = oldLinear;
            }
            return encMap;
        }

        function buildBlockEncryptMap(width, height, blockW, blockH, key) {
            const cols = Math.ceil(width / blockW), rows = Math.ceil(height / blockH);
            const totalBlocks = cols * rows;
            let seed = key ? simpleHash(key) : 123456;
            function rng() { seed = (seed * 9301 + 49297) % 233280; return seed / 233280; }
            const perm = Array.from({length: totalBlocks}, (_,i)=>i);
            for (let i=perm.length-1; i>0; i--) { const j = Math.floor(rng() * (i+1)); [perm[i], perm[j]] = [perm[j], perm[i]]; }
            const blocks = [];
            for (let r=0; r<rows; r++) for (let c=0; c<cols; c++) {
                const x = c*blockW, y = r*blockH, w = Math.min(blockW, width-x), h = Math.min(blockH, height-y);
                blocks.push({x, y, w, h, idx: r*cols + c});
            }
            const encMap = new Uint32Array(width * height);
            for (let dstIdx = 0; dstIdx < width*height; dstIdx++) {
                const dstY = Math.floor(dstIdx / width), dstX = dstIdx % width;
                const dstCol = Math.floor(dstX / blockW), dstRow = Math.floor(dstY / blockH);
                const dstBlockIdx = dstRow * cols + dstCol;
                const srcBlockIdx = perm[dstBlockIdx];
                const srcBlock = blocks[srcBlockIdx];
                const localX = dstX - dstCol*blockW, localY = dstY - dstRow*blockH;
                let srcX = srcBlock.x + localX, srcY = srcBlock.y + localY;
                if (srcX >= width) srcX = width-1; if (srcY >= height) srcY = height-1;
                encMap[dstIdx] = srcY * width + srcX;
            }
            return encMap;
        }
        function invertMap(map, len) { const inv = new Uint32Array(len); for (let i=0; i<len; i++) inv[map[i]] = i; return inv; }

        async function imageDataToBlob(imageData, width, height, format) {
            const surface = createCanvasSurface(width, height);
            surface.ctx.putImageData(imageData, 0, 0);
            return canvasToBlobCompat(surface.canvas, getImageExportOptions(format));
        }

        async function blobToImageData(blob) {
            if (!blob || blob.size === 0) {
                throw new Error('Invalid blob: empty or null');
            }
            const imageSource = await loadImageSource(blob);
            try {
                const w = imageSource.width, h = imageSource.height;
                if (!w || !h || w <= 0 || h <= 0) {
                    throw new Error('Invalid bitmap dimensions: ' + w + 'x' + h);
                }
                const surface = createCanvasSurface(w, h);
                surface.ctx.drawImage(imageSource.source, 0, 0);
                const imageData = surface.ctx.getImageData(0, 0, w, h);
                return { imageData, width: w, height: h };
            } finally {
                imageSource.cleanup();
            }
        }

        async function processImage(file, mode, blockW, blockH, shouldApplyXOR) {
            const imageSource = await loadImageSource(file);
            let width = imageSource.width, height = imageSource.height;
            const surface = createCanvasSurface(width, height);
            const canvas = surface.canvas;
            const ctx = surface.ctx;
            try {
                ctx.drawImage(imageSource.source, 0, 0);
            } finally {
                imageSource.cleanup();
            }
            let imageData = ctx.getImageData(0, 0, width, height);
            let data = imageData.data;
            const keyStr = keyInput.value || '';

            if (imgMethod === 'fastest') {
                if (mode === 'encrypt' && shouldApplyXOR) {
                    applyXOR(data, getFixedXORKey(keyStr));
                }
                imageData = processFastestImageData(imageData, mode, 1);
                width = imageData.width;
                height = imageData.height;
                data = imageData.data;
                if (mode === 'decrypt' && shouldApplyXOR) {
                    applyXOR(data, getFixedXORKey(keyStr));
                }
                canvas.width = width;
                canvas.height = height;
                ctx.putImageData(imageData, 0, 0);
                const exportOptions = getImageExportOptions(imgFormatSelect.value);
                const blob = await canvasToBlobCompat(canvas, exportOptions);
                const actualMime = blob.type || exportOptions.type;
                const ext = actualMime.split('/')[1];
                const inputName = file.name || 'image';
                let baseName = inputName.replace(/\.[^/.]+$/, '');
                baseName = baseName.replace(/_encrypted$|_decrypted$/g, '');
                const suffix = (mode==='encrypt'?'_encrypted':'_decrypted');
                return { blob, name: `${baseName}${suffix}.${ext}` };
            }
            
            if (mode === 'encrypt') {
                if (shouldApplyXOR) {
                    const xorKey = getFixedXORKey(keyStr);
                    applyXOR(data, xorKey);
                    const webpBlob = await imageDataToBlob(imageData, width, height, 'webp');
                    const result = await blobToImageData(webpBlob);
                    imageData = result.imageData;
                    data = imageData.data;
                    width = result.width;
                    height = result.height;
                }
                const totalPixels = width * height;
                let newData = null;
                try {
                    newData = await processImagePixelsWithWasm(data, width, height, 'encrypt', blockW, blockH, keyStr, 1, false);
                } catch (error) {
                    }
                if (!newData) {
                    let cacheKey = (imgMethod === 'gilbert') ? `gilbert:${width}:${height}:${keyStr}` : `block:${width}:${height}:${keyStr}:${blockW}:${blockH}`;
                    let encMap;
                    const cachedMap = getMapCache(cacheKey);
                    if (cachedMap && cachedMap.encMap) {
                        encMap = cachedMap.encMap;
                    } else {
                        if (imgMethod === 'gilbert') encMap = buildGilbertEncryptMap(width, height, keyStr);
                        else encMap = buildBlockEncryptMap(width, height, blockW, blockH, keyStr);
                        setMapCache(cacheKey, Object.assign({}, cachedMap || {}, { encMap }));
                    }
                    newData = await remapImagePixelsWithGpuFallback(data, encMap, width, height);
                    } else {
                    }
                data = newData;
                imageData = new ImageData(newData, width, height);
            } else {
                const totalPixels = width * height;
                let newData = null;
                try {
                    newData = await processImagePixelsWithWasm(data, width, height, 'decrypt', blockW, blockH, keyStr, 1, false);
                } catch (error) {
                    }
                if (!newData) {
                    let cacheKey = (imgMethod === 'gilbert') ? `gilbert:${width}:${height}:${keyStr}` : `block:${width}:${height}:${keyStr}:${blockW}:${blockH}`;
                    let invMap;
                    const cachedMap = getMapCache(cacheKey);
                    if (cachedMap) {
                        invMap = cachedMap.invMap;
                    }
                    if (!invMap) {
                        let encMap;
                        if (imgMethod === 'gilbert') encMap = buildGilbertEncryptMap(width, height, keyStr);
                        else encMap = buildBlockEncryptMap(width, height, blockW, blockH, keyStr);
                        invMap = invertMap(encMap, totalPixels);
                        setMapCache(cacheKey, Object.assign({}, cachedMap || {}, { invMap }));
                    }
                    newData = await remapImagePixelsWithGpuFallback(data, invMap, width, height);
                    } else {
                    }
                data = newData;
                imageData = new ImageData(newData, width, height);
                
                if (shouldApplyXOR) {
                    const webpBlob = await imageDataToBlob(imageData, width, height, 'webp');
                    const result = await blobToImageData(webpBlob);
                    imageData = result.imageData;
                    data = imageData.data;
                    width = result.width;
                    height = result.height;
                    const xorKey = getFixedXORKey(keyStr);
                    applyXOR(data, xorKey);
                }
            }
            
            canvas.width = width;
            canvas.height = height;
            ctx.putImageData(imageData, 0, 0);
            const exportOptions = getImageExportOptions(imgFormatSelect.value);
            const blob = await canvasToBlobCompat(canvas, exportOptions);
            const actualMime = blob.type || exportOptions.type;
            const ext = actualMime.split('/')[1];
            const inputName = file.name || 'image';
            let baseName = inputName.replace(/\.[^/.]+$/, '');
            baseName = baseName.replace(/_encrypted$|_decrypted$/g, '');
            const suffix = (mode==='encrypt'?'_encrypted':'_decrypted');
            return { blob, name: `${baseName}${suffix}.${ext}` };
        }

        function getImageRemapForMode(mode, width, height, blockW, blockH, keyStr) {
            const totalPixels = width * height;
            const cacheKey = (imgMethod === 'gilbert')
                ? `gilbert:${width}:${height}:${keyStr}`
                : `block:${width}:${height}:${keyStr}:${blockW}:${blockH}`;
            const cachedMap = getMapCache(cacheKey);
            if (mode === 'encrypt') {
                if (cachedMap && cachedMap.encMap) return cachedMap.encMap;
                const encMap = imgMethod === 'gilbert'
                    ? buildGilbertEncryptMap(width, height, keyStr)
                    : buildBlockEncryptMap(width, height, blockW, blockH, keyStr);
                setMapCache(cacheKey, Object.assign({}, cachedMap || {}, { encMap }));
                return encMap;
            }
            if (cachedMap && cachedMap.invMap) return cachedMap.invMap;
            const encMap = cachedMap && cachedMap.encMap
                ? cachedMap.encMap
                : (imgMethod === 'gilbert'
                    ? buildGilbertEncryptMap(width, height, keyStr)
                    : buildBlockEncryptMap(width, height, blockW, blockH, keyStr));
            const invMap = invertMap(encMap, totalPixels);
            setMapCache(cacheKey, Object.assign({}, cachedMap || {}, { encMap, invMap }));
            return invMap;
        }

        async function processImageBatchInMemory(file, mode, blockW, blockH, count, shouldApplyXOR, format) {
            const imageSource = await loadImageSource(file);
            let width = imageSource.width, height = imageSource.height;
            const surface = createCanvasSurface(width, height);
            const canvas = surface.canvas;
            const ctx = surface.ctx;
            try {
                ctx.drawImage(imageSource.source, 0, 0);
            } finally {
                imageSource.cleanup();
            }

            let imageData = ctx.getImageData(0, 0, width, height);
            let data = imageData.data;
            const keyStr = keyInput.value || '';

            if (imgMethod === 'fastest') {
                if (mode === 'encrypt' && shouldApplyXOR) {
                    applyXOR(data, getFixedXORKey(keyStr));
                }
                imageData = processFastestImageData(imageData, mode, count);
                width = imageData.width;
                height = imageData.height;
                data = imageData.data;
                if (mode === 'decrypt' && shouldApplyXOR) {
                    applyXOR(data, getFixedXORKey(keyStr));
                }
                canvas.width = width;
                canvas.height = height;
                ctx.putImageData(imageData, 0, 0);
                const exportOptions = getImageExportOptions(format);
                const blob = await canvasToBlobCompat(canvas, exportOptions);
                const actualMime = blob.type || exportOptions.type;
                const ext = actualMime.split('/')[1];
                const inputName = file.name || 'image';
                let baseName = inputName.replace(/\.[^/.]+$/, '');
                baseName = baseName.replace(/_encrypted$|_decrypted$/g, '');
                const suffix = mode === 'encrypt' ? '_encrypted' : '_decrypted';
                return { blob, name: `${baseName}${suffix}.${ext}` };
            }
            let wasmData = null;
            try {
                wasmData = await processImagePixelsWithWasm(data, width, height, mode, blockW, blockH, keyStr, count, shouldApplyXOR);
            } catch (error) {
                }

            if (wasmData) {
                data = wasmData;
                } else {
                if (mode === 'encrypt' && shouldApplyXOR) {
                    applyXOR(data, getFixedXORKey(keyStr));
                }

                for (let i = 0; i < count; i++) {
                    const remap = getImageRemapForMode(mode, width, height, blockW, blockH, keyStr);
                    data = await remapImagePixelsWithGpuFallback(data, remap, width, height);
                    await yieldToBrowser();
                }

                if (mode === 'decrypt' && shouldApplyXOR) {
                    applyXOR(data, getFixedXORKey(keyStr));
                }
                }
            imageData = new ImageData(data, width, height);

            canvas.width = width;
            canvas.height = height;
            ctx.putImageData(imageData, 0, 0);
            const exportOptions = getImageExportOptions(format);
            const blob = await canvasToBlobCompat(canvas, exportOptions);
            const actualMime = blob.type || exportOptions.type;
            const ext = actualMime.split('/')[1];
            const inputName = file.name || 'image';
            let baseName = inputName.replace(/\.[^/.]+$/, '');
            baseName = baseName.replace(/_encrypted$|_decrypted$/g, '');
            const suffix = mode === 'encrypt' ? '_encrypted' : '_decrypted';
            return { blob, name: `${baseName}${suffix}.${ext}` };
        }

        async function updateFirstImageCache() {
            if (selectedImageFiles.length === 0) { cachedFirstImageWidth = cachedFirstImageHeight = null; cachedFirstImageName = ''; return; }
            try {
                const file = selectedImageFiles[0];
                const knownInfo = largeImageInfos.find(info => info.index === 0 && info.name === (file.name || 'image') && info.size === (file.size || 0));
                if (knownInfo) {
                    cachedFirstImageWidth = knownInfo.width;
                    cachedFirstImageHeight = knownInfo.height;
                    cachedFirstImageName = file.name;
                    return;
                }
                const imageSource = await loadImageSource(file);
                cachedFirstImageWidth = imageSource.width; cachedFirstImageHeight = imageSource.height; cachedFirstImageName = file.name;
                imageSource.cleanup();
            } catch (e) { cachedFirstImageWidth = cachedFirstImageHeight = null; cachedFirstImageName = ''; }
        }

        function mergeLargeImageInfos(newInfos) {
            if (!newInfos || !newInfos.length) return;
            const byIndex = new Map(largeImageInfos.map(info => [info.index, info]));
            newInfos.forEach(info => {
                if (info) byIndex.set(info.index, info);
            });
            largeImageInfos = Array.from(byIndex.values()).sort((a, b) => a.index - b.index);
        }

        function scheduleImportFallbackDimensionWork(files, importSequence, fallbackIndexes, hadImmediateLargeWarning) {
            if (!fallbackIndexes.length) return;
            window.setTimeout(async () => {
                const decodedInfos = await inspectImageFallbacks(files, fallbackIndexes, new Array(files.length));
                if (importSequence !== imageImportSequence || selectedImageFiles !== files) return;
                const knownLargeIndexes = new Set(largeImageInfos.filter(info => info.isLarge).map(info => info.index));
                mergeLargeImageInfos(decodedInfos);
                const newlyLargeInfos = decodedInfos.filter(info => info && info.isLarge && !knownLargeIndexes.has(info.index));
                if (newlyLargeInfos.length && isLargeImageWarningEnabled && !hadImmediateLargeWarning && !isProcessing) {
                    const largeCount = largeImageInfos.filter(info => info.isLarge).length;
                    selectedCountDisplay.value = `导入${selectedImageFiles.length}张图片，${largeCount}张大图`;
                    showLargeImageImportWarning(newlyLargeInfos);
                }
                if (imgMethod === 'block' && encryptMethodModal.style.display === 'flex') updateBlockSizeOptions();
            }, 0);
        }

        function schedulePostImportDimensionWork() {
            window.setTimeout(() => {
                updateFirstImageCache().then(() => {
                    if (imgMethod === 'block' && encryptMethodModal.style.display === 'flex') updateBlockSizeOptions();
                });
            }, 0);
        }

        function fillBlockOptions(width, height) {
            const widthFactors = [], heightFactors = [];
            for (let i = 1; i <= width; i++) if (width % i === 0) widthFactors.push(i);
            for (let i = 1; i <= height; i++) if (height % i === 0) heightFactors.push(i);
            imgBlockWidthSelect.innerHTML = widthFactors.map(v => `<option value="${v}">${v}</option>`).join('');
            imgBlockHeightSelect.innerHTML = heightFactors.map(v => `<option value="${v}">${v}</option>`).join('');
            imgBlockWidthSelect.value = widthFactors.includes(imgBlockW) ? String(imgBlockW) : '1';
            imgBlockHeightSelect.value = heightFactors.includes(imgBlockH) ? String(imgBlockH) : '1';
            imgBlockW = parseInt(imgBlockWidthSelect.value, 10);
            imgBlockH = parseInt(imgBlockHeightSelect.value, 10);
            imgBlockWidthSelect.disabled = false; imgBlockHeightSelect.disabled = false; standardizeBtn.disabled = false;
            imgBlockWidthSelect.size = Math.min(5, imgBlockWidthSelect.options.length);
            imgBlockHeightSelect.size = Math.min(5, imgBlockHeightSelect.options.length);
            updateBlockHintAndVars();
        }
        function updateBlockHintAndVars() {
            if (selectedImageFiles.length === 0 || !cachedFirstImageWidth) { blockHint.innerText = '请先选择图片'; return; }
            const w = parseInt(imgBlockWidthSelect.value,10); const h = parseInt(imgBlockHeightSelect.value,10);
            if (isNaN(w)||isNaN(h)||w===0||h===0) return;
            if (cachedFirstImageWidth % w !== 0 || cachedFirstImageHeight % h !== 0) blockHint.innerText = '警告：块大小不能整除图像，将产生不完整块';
            else { const rows = cachedFirstImageWidth / w; const cols = cachedFirstImageHeight / h; blockHint.innerText = `可用分块：${rows} 列 × ${cols} 行 = ${rows*cols} 块`; }
            imgBlockW = w; imgBlockH = h;
        }
        async function updateBlockSizeOptions() {
            imgBlockWidthSelect.disabled = true; imgBlockHeightSelect.disabled = true; standardizeBtn.disabled = true;
            if (selectedImageFiles.length === 0) {
                imgBlockWidthSelect.innerHTML = '<option>请先选择图片</option>'; imgBlockHeightSelect.innerHTML = '<option>请先选择图片</option>'; blockHint.innerText = ''; return;
            }
            if (selectedImageFiles.length > 1) {
                imgBlockWidthSelect.innerHTML = '<option value="1" selected>1 (多文件模式)</option>'; imgBlockHeightSelect.innerHTML = '<option value="1" selected>1 (多文件模式)</option>';
                imgBlockW = 1; imgBlockH = 1; blockHint.innerText = '多文件模式下块大小固定为1×1（像素级打乱）';
                imgBlockWidthSelect.disabled = false; imgBlockHeightSelect.disabled = false; standardizeBtn.disabled = true;
                imgBlockWidthSelect.size = 1; imgBlockHeightSelect.size = 1; return;
            }
            const file = selectedImageFiles[0];
            if (cachedFirstImageName === file.name && cachedFirstImageWidth && cachedFirstImageHeight) fillBlockOptions(cachedFirstImageWidth, cachedFirstImageHeight);
            else {
                imgBlockWidthSelect.innerHTML = '<option>加载尺寸中…</option>'; imgBlockHeightSelect.innerHTML = '<option>加载尺寸中…</option>'; blockHint.innerText = '正在解析图片…';
                await updateFirstImageCache();
                if (selectedImageFiles[0] === file && cachedFirstImageName === file.name && cachedFirstImageWidth) fillBlockOptions(cachedFirstImageWidth, cachedFirstImageHeight);
                else { imgBlockWidthSelect.innerHTML = '<option>无法读取图片</option>'; imgBlockHeightSelect.innerHTML = '<option>无法读取图片</option>'; blockHint.innerText = '读取失败'; }
            }
        }

        function disableExportControls() { imgFormatSelect.disabled = true; startEncrypt.disabled = true; startDecrypt.disabled = true; }
        function enableExportControls() { imgFormatSelect.disabled = false; startEncrypt.disabled = false; startDecrypt.disabled = false; }

        function processFastestImageData(imageData, mode, rounds) {
            if (!window.FastestObfuscation || typeof window.FastestObfuscation.fastEncrypt !== 'function') {
                throw new Error('最速混淆模块未加载');
            }
            const key = 1;  // 硬编码为 1，与小程序默认密钥一致
            let data = imageData.data;
            const width = imageData.width;
            const height = imageData.height;
            const isEncrypt = mode === 'encrypt';
            for (let i = 0; i < Math.max(1, rounds || 1); i++) {
                data = isEncrypt
                    ? window.FastestObfuscation.fastEncrypt(data, width, height, key)
                    : window.FastestObfuscation.fastDecrypt(data, width, height, key);
            }
            return new ImageData(data, width, height);
        }

        function getImageMethodLabel(method) {
            if (method === 'gilbert') return '吉尔伯特曲线';
            if (method === 'block') return '分块打乱';
            if (method === 'fastest') return '最速混淆';
            return method || '';
        }

        function saveImageMethodSettings() {
            const settings = {
                method: imgMethod,
                blockW: imgBlockW,
                blockH: imgBlockH
            };
            localStorage.setItem(IMAGE_METHOD_SETTINGS_STORAGE_KEY, JSON.stringify(settings));
        }

        function restoreImageMethodSettings() {
            try {
                const raw = localStorage.getItem(IMAGE_METHOD_SETTINGS_STORAGE_KEY);
                if (!raw) {
                    currentMethodDisplay.innerText = getImageMethodLabel(imgMethod);
                    return;
                }
                const settings = JSON.parse(raw);
                if (settings && ['gilbert', 'block', 'fastest'].includes(settings.method)) {
                    imgMethod = settings.method;
                }
                const savedBlockW = parseInt(settings && settings.blockW, 10);
                const savedBlockH = parseInt(settings && settings.blockH, 10);
                if (!isNaN(savedBlockW) && savedBlockW > 0) imgBlockW = savedBlockW;
                if (!isNaN(savedBlockH) && savedBlockH > 0) imgBlockH = savedBlockH;
                currentMethodDisplay.innerText = getImageMethodLabel(imgMethod);
            } catch (error) {
                currentMethodDisplay.innerText = getImageMethodLabel(imgMethod);
            }
        }

        xorCompatibilityReady = applyImageCompatibility();

        function resetToOriginal() {
            if (isProcessing) { alert('请等待当前处理完成'); return; }
            if (!selectedImageFiles.length) { alert('没有已选择的图片'); return; }
            previewUrls.forEach(url => URL.revokeObjectURL(url));
            previewUrls = selectedImageFiles.map(f => URL.createObjectURL(f));
            currentPreviewIndex = 0; latestProcessedImages = []; latestKeyParams = null;
            downloadAllBtn.classList.remove('highlight');
            imageProgress.value = 0; selectedCountDisplay.value = `导入${selectedImageFiles.length}张图片`;
            enableExportControls();
            clearTransientImageCache();
            encryptCount = 0;
            xorAppliedForEncrypt = false;
            xorAppliedForDecrypt = false;
            updateEncryptCounter();
            if (previewModal.style.display === 'flex' && previewUrls.length) { previewImg.src = previewUrls[0]; previewCounter.innerText = `1 / ${previewUrls.length}`; }
        }

        restoreImageMethodSettings();

        async function handleImages(mode) {
            if (isProcessing) return; if (!selectedImageFiles.length) { alert('请先选择图片文件'); return; }
            isProcessing = true; disableExportControls();
            beginImageProcessingKeepAlive();
            try {
                await xorCompatibilityReady;
                imageProgress.value = 0; downloadAllBtn.classList.remove('highlight');
                selectedCountDisplay.value = mode === 'encrypt' ? '加密中' : '解密中';
                let currentBlockW = imgBlockW, currentBlockH = imgBlockH;
                if (imgMethod === 'block' && selectedImageFiles.length > 1) { currentBlockW = 1; currentBlockH = 1; }
                else if (imgMethod === 'block' && selectedImageFiles.length === 1) {
                    const wVal = parseInt(imgBlockWidthSelect.value,10); const hVal = parseInt(imgBlockHeightSelect.value,10);
                    currentBlockW = (isNaN(wVal)||wVal<1) ? 1 : wVal; currentBlockH = (isNaN(hVal)||hVal<1) ? 1 : hVal;
                }
                const total = selectedImageFiles.length; const results = new Array(total); let completed = 0;
                const previousProcessedImages = [...latestProcessedImages];
                latestProcessedImages = [];
                latestKeyParams = null;
                
                const effectiveXOREnabled = batchXORStateOverride === null ? isXOREnabled : batchXORStateOverride;
                const allowRepeatXOR = isReencryptEnabled && batchXORStateOverride === null;
                let shouldApplyXOR = false;
                if (mode === 'encrypt') {
                    shouldApplyXOR = effectiveXOREnabled && (allowRepeatXOR || !xorAppliedForEncrypt);
                } else {
                    shouldApplyXOR = effectiveXOREnabled && (allowRepeatXOR || !xorAppliedForDecrypt);
                }
                if (shouldApplyXOR && imageRuntime.webpTranscodeSupported === false) {
                    shouldApplyXOR = false;
                }
                
                try {
                    for (let idx = 0; idx < total; idx++) {
                        const file = selectedImageFiles[idx];
                        let inputFile = file;
                        if (previousProcessedImages.length > 0 && idx < previousProcessedImages.length) {
                            const prevResult = previousProcessedImages[idx];
                            if (prevResult) {
                                inputFile = createFileLike(prevResult.blob, prevResult.name);
                            }
                            previousProcessedImages[idx] = null;
                        }
                        const { blob, name } = await processImage(inputFile, mode, currentBlockW, currentBlockH, shouldApplyXOR);
                        inputFile = null;
                        results[idx] = { blob, name };
                        completed++;
                        selectedCountDisplay.value = `完成${completed}张图片`;
                        imageProgress.value = Math.round((completed/total)*100);
                        await yieldToBrowser();
                    }
                } finally {
                    previousProcessedImages.length = 0;
                }
                latestProcessedImages = results.filter(r => r !== undefined);
                previewUrls.forEach(url => URL.revokeObjectURL(url));
                previewUrls = latestProcessedImages.map(r => URL.createObjectURL(r.blob));
                currentPreviewIndex = 0;
                const formatText = imgFormatSelect.options[imgFormatSelect.selectedIndex].text;
                downloadAllBtn.classList.add('highlight'); 
                selectedCountDisplay.value = `完成${results.length}张图片`;
                if (previewModal.style.display === 'flex' && previewUrls.length) { previewImg.src = previewUrls[0]; previewCounter.innerText = `1 / ${previewUrls.length}`; }
                if (mode === 'encrypt') {
                    encryptCount++;
                } else if (mode === 'decrypt') {
                    encryptCount--;
                }
                updateEncryptCounter();
                if (shouldApplyXOR) {
                    if (mode === 'encrypt') {
                        xorAppliedForEncrypt = true;
                        xorAppliedForDecrypt = false;
                    } else {
                        xorAppliedForDecrypt = true;
                        xorAppliedForEncrypt = false;
                    }
                }
                latestKeyParams = { key: keyInput.value, method: imgMethod, blockW: currentBlockW, blockH: currentBlockH, format: imgFormatSelect.value, count: encryptCount, xorEnabled: effectiveXOREnabled, xorKey: effectiveXOREnabled ? XOR_FIXED_KEY : null };
                if (isReencryptEnabled) {
                    enableExportControls();
                }
            } catch (e) { alert(`处理失败: ${e.message}`); enableExportControls(); latestProcessedImages = []; previewUrls.forEach(url => URL.revokeObjectURL(url)); previewUrls = selectedImageFiles.map(f => URL.createObjectURL(f)); imageProgress.value = 0; selectedCountDisplay.value = `导入${selectedImageFiles.length}张图片`; }
            finally {
                isProcessing = false;
                endImageProcessingKeepAlive();
            }
        }

        async function downloadAll() {
            if (!latestProcessedImages.length) { alert('请先执行加密或解密操作'); return; }
            const usePack = packCheck.checked;
            const ZipCtor = usePack ? await ensureJSZip() : null;
            const zip = usePack ? new ZipCtor() : null;
            const results = latestProcessedImages;
            if (usePack) {
                results.forEach(r => zip.file(r.name, r.blob));
                if (exportKeyCheck.checked && latestKeyParams) {
                    const p = latestKeyParams;
                    let keyText = `# 加密参数\n密钥: ${p.key}\n方式: ${getImageMethodLabel(p.method)}\n`;
                    if (p.method === 'block') { keyText += `块宽: ${p.blockW}\n块高: ${p.blockH}\n`; }
                    keyText += `XOR二次加密: ${p.xorEnabled ? '开启 (密钥: ' + p.xorKey + ')' : '关闭'}\n`;
                    keyText += `导出格式: ${p.format}\n处理次数: ${p.count}\n`;
                    zip.file('key_and_params.txt', keyText);
                }
                const content = await zip.generateAsync({ type: 'blob' });
                saveAs(content, `processed_images_${Date.now()}.zip`);
            } else {
                results.forEach(r => saveAs(r.blob, r.name));
                if (exportKeyCheck.checked && latestKeyParams) {
                    const p = latestKeyParams;
                    let keyText = `密钥: ${p.key}\n方式: ${getImageMethodLabel(p.method)}\n`;
                    if (p.method === 'block') { keyText += `块宽: ${p.blockW}\n块高: ${p.blockH}\n`; }
                    keyText += `XOR二次加密: ${p.xorEnabled ? '开启 (密钥: ' + p.xorKey + ')' : '关闭'}\n`;
                    keyText += `导出格式: ${p.format}\n处理次数: ${p.count}`;
                    saveAs(new Blob([keyText], { type: 'text/plain;charset=utf-8' }), 'key_params.txt');
                }
            }
        }
        async function exportToFolder() {
            if (!latestProcessedImages.length) { alert('请先执行加密或解密操作'); return; }
            if (!window.showDirectoryPicker) { downloadAll(); return; }
            try {
                const dirHandle = await window.showDirectoryPicker();
                for (const img of latestProcessedImages) {
                    const fileHandle = await dirHandle.getFileHandle(img.name, { create: true });
                    const writable = await fileHandle.createWritable(); await writable.write(img.blob); await writable.close();
                }
                if (exportKeyCheck.checked && latestKeyParams) {
                    const p = latestKeyParams;
                    let keyText = `密钥: ${p.key}\n方式: ${getImageMethodLabel(p.method)}\n`;
                    if (p.method === 'block') { keyText += `块宽: ${p.blockW}\n块高: ${p.blockH}\n`; }
                    keyText += `XOR二次加密: ${p.xorEnabled ? '开启 (密钥: ' + p.xorKey + ')' : '关闭'}\n`;
                    keyText += `导出格式: ${p.format}\n处理次数: ${p.count}`;
                    const keyBlob = new Blob([keyText], { type: 'text/plain;charset=utf-8' });
                    const keyHandle = await dirHandle.getFileHandle('key_params.txt', { create: true });
                    const writable = await keyHandle.createWritable(); await writable.write(keyBlob); await writable.close();
                }
                alert(`成功导出 ${latestProcessedImages.length} 张图片到所选文件夹。`);
            } catch (err) { if (err.name !== 'AbortError') { alert('导出失败：' + err.message); } }
        }

        // 事件绑定
        browseBtn.addEventListener('click', () => {
            if (isProcessing) {
                alert('正在处理中，请等待完成或点击还原');
                return;
            }
            // Image picker only: always reopen the image file dialog.
            imagePicker.value = '';
            imagePicker.setAttribute('accept', 'image/*');
            imagePicker.click();
        });
        imagePicker.addEventListener('change', async function(e) {
            if (isProcessing) { alert('正在处理中，请等待完成或点击还原'); return; }
            const files = Array.from(e.target.files).filter(file => file && file.type && file.type.startsWith('image/'));
            if (!files.length) { alert('请选择图片文件'); return; }
            const importSequence = ++imageImportSequence;
            selectedImageFiles = files;
            previewUrls.forEach(url => URL.revokeObjectURL(url));
            previewUrls = files.map(f => URL.createObjectURL(f));
            latestProcessedImages = []; latestKeyParams = null;
            clearTransientImageCache();
            // 显示导入了x张图片的状态
            selectedCountDisplay.value = `导入了${files.length}张图片，正在读取分辨率`;
            imageProgress.value = 0;
            downloadAllBtn.classList.remove('highlight'); enableExportControls();
            encryptCount = 0;
            updateEncryptCounter();
            const headerInspection = await inspectImageHeaders(files);
            if (importSequence !== imageImportSequence) return;
            largeImageInfos = headerInspection.infos.filter(Boolean);
            const largeInfos = largeImageInfos.filter(info => info.isLarge);
            const hasImmediateLargeWarning = largeInfos.length && isLargeImageWarningEnabled;
            if (largeInfos.length) {
                selectedCountDisplay.value = '\u5bfc\u5165' + files.length + '\u5f20\u56fe\u7247\uff0c' + largeInfos.length + '\u5f20\u5927\u56fe';
                if (isLargeImageWarningEnabled) showLargeImageImportWarning(largeInfos);
                else schedulePostImportDimensionWork();
            } else {
                selectedCountDisplay.value = `导入了${files.length}张图片`;
                schedulePostImportDimensionWork();
            }
            scheduleImportFallbackDimensionWork(files, importSequence, headerInspection.fallbackIndexes, hasImmediateLargeWarning);
        });
        viewPreviewBtn.addEventListener('click', () => {
            if (previewUrls.length === 0) { alert('请先选择图片'); return; }
            currentPreviewIndex = 0; previewImg.src = previewUrls[0]; previewCounter.innerText = `1 / ${previewUrls.length}`; previewModal.style.display = 'flex';
        });
        window.addEventListener('click', (e) => { if (e.target === previewModal) previewModal.style.display = 'none'; });
        prevBtn.addEventListener('click', () => { if (previewUrls.length === 0) return; currentPreviewIndex = (currentPreviewIndex - 1 + previewUrls.length) % previewUrls.length; previewImg.src = previewUrls[currentPreviewIndex]; previewCounter.innerText = `${currentPreviewIndex+1} / ${previewUrls.length}`; });
        nextBtn.addEventListener('click', () => { if (previewUrls.length === 0) return; currentPreviewIndex = (currentPreviewIndex + 1) % previewUrls.length; previewImg.src = previewUrls[currentPreviewIndex]; previewCounter.innerText = `${currentPreviewIndex+1} / ${previewUrls.length}`; });
        // 点击预览计数器关闭预览窗口
        previewCounter.addEventListener('click', () => {
            previewModal.style.display = 'none';
        });
        startEncrypt.addEventListener('click', () => handleImages('encrypt'));
        startDecrypt.addEventListener('click', () => handleImages('decrypt'));
        downloadAllBtn.addEventListener('click', downloadAll);
        exportConfigBtn.addEventListener('click', exportToFolder);
        resetBtn.addEventListener('click', resetToOriginal);
        
        imgFormatSelect.addEventListener('change', function() {
            if (batchFormatSelect) batchFormatSelect.value = this.value;
        });
        batchFormatSelect.addEventListener('change', function() {
            imgFormatSelect.value = this.value;
        });
        
        // 批量处理功能
        const batchProcessModal = document.getElementById('batchProcessModal');
        const encryptCounterEl = document.getElementById('encryptCounter');
        let longPressTimer = null;
        
        encryptCounterEl.addEventListener('mousedown', () => {
            longPressTimer = setTimeout(() => { batchProcessModal.style.display = 'flex'; }, 200);
        });
        encryptCounterEl.addEventListener('mouseup', () => clearTimeout(longPressTimer));
        encryptCounterEl.addEventListener('mouseleave', () => clearTimeout(longPressTimer));
        encryptCounterEl.addEventListener('touchstart', (e) => {
            longPressTimer = setTimeout(() => { batchProcessModal.style.display = 'flex'; }, 200);
        }, { passive: true });
        encryptCounterEl.addEventListener('touchend', () => clearTimeout(longPressTimer));
        
        async function executeBatchProcess() {
            await xorCompatibilityReady;
            const mode = document.querySelector('input[name="batchMode"]:checked').value;
            const count = parseInt(document.getElementById('batchCount').value, 10);
            const format = batchFormatSelect.value;
            
            if (!selectedImageFiles.length) { alert('请先选择图片'); return; }
            if (isNaN(count) || count < 1) { alert('请输入有效次数'); return; }
            
            const originalFormat = imgFormatSelect.value;
            batchProcessModal.style.display = 'none';
            
            if (isProcessing) return;
            isProcessing = true;
            disableExportControls();
            beginImageProcessingKeepAlive();

            try {
                imageProgress.value = 0;
                downloadAllBtn.classList.remove('highlight');
                selectedCountDisplay.value = mode === 'encrypt' ? '批量加密中' : '批量解密中';

                let currentBlockW = imgBlockW, currentBlockH = imgBlockH;
                if (imgMethod === 'block' && selectedImageFiles.length > 1) {
                    currentBlockW = 1;
                    currentBlockH = 1;
                } else if (imgMethod === 'block' && selectedImageFiles.length === 1) {
                    const wVal = parseInt(imgBlockWidthSelect.value, 10);
                    const hVal = parseInt(imgBlockHeightSelect.value, 10);
                    currentBlockW = (isNaN(wVal) || wVal < 1) ? 1 : wVal;
                    currentBlockH = (isNaN(hVal) || hVal < 1) ? 1 : hVal;
                }

                const previousProcessedImages = [...latestProcessedImages];
                const results = new Array(selectedImageFiles.length);
                latestProcessedImages = [];
                latestKeyParams = null;
                const shouldApplyXOR = isXOREnabled && imageRuntime.webpTranscodeSupported !== false;
                imgFormatSelect.value = format;

                try {
                    for (let idx = 0; idx < selectedImageFiles.length; idx++) {
                        let inputFile = selectedImageFiles[idx];
                        if (previousProcessedImages.length > 0 && idx < previousProcessedImages.length && previousProcessedImages[idx]) {
                            inputFile = createFileLike(previousProcessedImages[idx].blob, previousProcessedImages[idx].name);
                            previousProcessedImages[idx] = null;
                        }
                        results[idx] = await processImageBatchInMemory(inputFile, mode, currentBlockW, currentBlockH, count, shouldApplyXOR, format);
                        const completed = idx + 1;
                        selectedCountDisplay.value = `批量完成${completed}张图片`;
                        imageProgress.value = Math.round((completed / selectedImageFiles.length) * 100);
                        await yieldToBrowser();
                    }
                } finally {
                    previousProcessedImages.length = 0;
                }

                latestProcessedImages = results.filter(r => r !== undefined);
                previewUrls.forEach(url => URL.revokeObjectURL(url));
                previewUrls = latestProcessedImages.map(r => URL.createObjectURL(r.blob));
                currentPreviewIndex = 0;
                downloadAllBtn.classList.add('highlight');
                selectedCountDisplay.value = `批量完成${latestProcessedImages.length}张图片`;
                if (previewModal.style.display === 'flex' && previewUrls.length) {
                    previewImg.src = previewUrls[0];
                    previewCounter.innerText = `1 / ${previewUrls.length}`;
                }

                encryptCount += mode === 'encrypt' ? count : -count;
                updateEncryptCounter();
                if (shouldApplyXOR) {
                    if (mode === 'encrypt') {
                        xorAppliedForEncrypt = true;
                        xorAppliedForDecrypt = false;
                    } else {
                        xorAppliedForDecrypt = true;
                        xorAppliedForEncrypt = false;
                    }
                }
                latestKeyParams = { key: keyInput.value, method: imgMethod, blockW: currentBlockW, blockH: currentBlockH, format, count: encryptCount, xorEnabled: isXOREnabled, xorKey: isXOREnabled ? XOR_FIXED_KEY : null };
                if (isReencryptEnabled) enableExportControls();
            } catch (e) {
                alert(`批量处理失败: ${e.message}`);
                enableExportControls();
                latestProcessedImages = [];
                previewUrls.forEach(url => URL.revokeObjectURL(url));
                previewUrls = selectedImageFiles.map(f => URL.createObjectURL(f));
                imageProgress.value = 0;
                selectedCountDisplay.value = `导入${selectedImageFiles.length}张图片`;
            } finally {
                batchXORStateOverride = null;
                imgFormatSelect.value = originalFormat;
                isProcessing = false;
                endImageProcessingKeepAlive();
                if (!isReencryptEnabled) enableExportControls();
            }
        }
        
        document.getElementById('executeBatchBtn').addEventListener('click', executeBatchProcess);
        window.addEventListener('click', (e) => { if (e.target === batchProcessModal) batchProcessModal.style.display = 'none'; });
        
        chooseMethodBtn.addEventListener('click', () => {
            document.querySelector(`input[name="imgEncryptMode"][value="${imgMethod}"]`).checked = true;
            imgBlockParamsDiv.style.display = imgMethod === 'block' ? 'block' : 'none';
            if (imgFastestParamsDiv) imgFastestParamsDiv.style.display = 'none';
            if (imgMethod === 'block') updateBlockSizeOptions();
            encryptMethodModal.style.display = 'flex';
        });
        imgEncryptRadios.forEach(radio => { radio.addEventListener('change', (e) => { const show = e.target.value === 'block'; imgBlockParamsDiv.style.display = show ? 'block' : 'none'; if (imgFastestParamsDiv) imgFastestParamsDiv.style.display = 'none'; if (show) updateBlockSizeOptions(); }); });
        standardizeBtn.addEventListener('click', () => {
            if (selectedImageFiles.length > 1) return;
            const wVal = imgBlockWidthSelect.value; if (!wVal) return;
            let exists = Array.from(imgBlockHeightSelect.options).some(opt => opt.value === wVal);
            if (!exists) { const newOpt = document.createElement('option'); newOpt.value = wVal; newOpt.text = wVal + ' (自定义)'; imgBlockHeightSelect.appendChild(newOpt); }
            imgBlockHeightSelect.value = wVal; imgBlockH = parseInt(wVal,10); updateBlockHintAndVars();
            imgBlockHeightSelect.size = Math.min(5, imgBlockHeightSelect.options.length);
        });
        saveEncryptMethodBtn.addEventListener('click', () => {
            const selected = document.querySelector('input[name="imgEncryptMode"]:checked').value;
            const previousMethod = imgMethod;
            imgMethod = selected;
            currentMethodDisplay.innerText = (selected === 'gilbert') ? '吉尔伯特曲线' : (selected === 'block' ? '分块打乱' : '最速混淆');
            // 自动切换导出格式：最速混淆 → PNG，其他 → JPG95
            if (selected === 'fastest') {
                imgFormatSelect.value = 'png';
            } else {
                imgFormatSelect.value = 'jpg95';
            }
            if (batchFormatSelect) batchFormatSelect.value = imgFormatSelect.value;
            if (selected === 'block') {
                if (selectedImageFiles.length > 1) { imgBlockW = 1; imgBlockH = 1; }
                else { const wVal = parseInt(imgBlockWidthSelect.value,10); const hVal = parseInt(imgBlockHeightSelect.value,10); imgBlockW = (isNaN(wVal)||wVal<1)?1:wVal; imgBlockH = (isNaN(hVal)||hVal<1)?1:hVal; }
            }
            saveImageMethodSettings();
            if (previousMethod !== selected) {
                clearTransientImageCache();
            }
            encryptMethodModal.style.display = 'none';
        });
        window.addEventListener('click', (e) => { if (e.target === encryptMethodModal) encryptMethodModal.style.display = 'none'; });
        imgBlockWidthSelect.addEventListener('change', () => { updateBlockHintAndVars(); if (imgMethod === 'block') saveImageMethodSettings(); });
        imgBlockHeightSelect.addEventListener('change', () => { updateBlockHintAndVars(); if (imgMethod === 'block') saveImageMethodSettings(); });
        // 图片预览全屏双指缩放功能
        let imgLastDistance = 0;
        let imgCurrentScale = 1;
        let imgScaleOrigin = { x: 0, y: 0 };

        previewImg.addEventListener('touchstart', (e) => {
            if (!document.fullscreenElement) return;

            // 双指触摸开始
            if (e.touches.length === 2) {
                const touch1 = e.touches[0];
                const touch2 = e.touches[1];
                imgLastDistance = Math.hypot(touch2.clientX - touch1.clientX, touch2.clientY - touch1.clientY);
                imgScaleOrigin.x = (touch1.clientX + touch2.clientX) / 2;
                imgScaleOrigin.y = (touch1.clientY + touch2.clientY) / 2;
            }
        }, { passive: true });

        previewImg.addEventListener('touchmove', (e) => {
            if (!document.fullscreenElement) return;

            // 双指触摸移动 - 缩放
            if (e.touches.length === 2) {
                e.preventDefault();
                const touch1 = e.touches[0];
                const touch2 = e.touches[1];
                const currentDistance = Math.hypot(touch2.clientX - touch1.clientX, touch2.clientY - touch1.clientY);
                
                if (imgLastDistance > 0) {
                    const scaleFactor = currentDistance / imgLastDistance;
                    imgCurrentScale *= scaleFactor;
                    // 限制缩放范围
                    imgCurrentScale = Math.max(0.5, Math.min(3, imgCurrentScale));
                    
                    // 应用缩放变换
                    previewImg.style.transform = `scale(${imgCurrentScale})`;
                    previewImg.style.transformOrigin = `${imgScaleOrigin.x}px ${imgScaleOrigin.y}px`;
                }
                
                imgLastDistance = currentDistance;
            }
        }, { passive: false });

        previewImg.addEventListener('touchend', (e) => {
            if (!document.fullscreenElement) return;
            
            // 重置缩放相关变量
            if (e.touches.length === 0) {
                imgLastDistance = 0;
            }
        });

        // 监听图片预览全屏状态变化
        document.addEventListener('fullscreenchange', () => {
            if (document.fullscreenElement && document.fullscreenElement === previewImg) {
                // 进入全屏
                imgCurrentScale = 1;
                imgLastDistance = 0;
                previewImg.style.transform = '';
                previewImg.style.transformOrigin = '';
            } else if (!document.fullscreenElement && document.pictureInPictureElement !== previewImg) {
                // 退出全屏
                imgCurrentScale = 1;
                imgLastDistance = 0;
                previewImg.style.transform = '';
                previewImg.style.transformOrigin = '';
            }
        });

        previewImg.addEventListener('click', function(e) { e.stopPropagation(); if (document.fullscreenElement) document.exitFullscreen(); else this.requestFullscreen(); });
        window.saveAs = window.saveAs || function(blob, name) { const link = document.createElement('a'); link.href = URL.createObjectURL(blob); link.download = name; link.click(); URL.revokeObjectURL(link.href); };
    })();

    // ==================== 标签页切换 & 刷新 (独立) ====================
    (function() {
        const tabVideo = document.getElementById('tabVideoDecode');
        const tabImage = document.getElementById('tabImageDecode');
        const pageVideo = document.getElementById('videoPage');
        const pageImage = document.getElementById('imagePage');
        const refreshBtn = document.getElementById('refreshCurrentBtn');

        function switchToTab(tab) {
            if (tab === 'video') {
                tabVideo.classList.add('active'); tabImage.classList.remove('active');
                pageVideo.classList.add('active-page'); pageImage.classList.remove('active-page');
                if (typeof window.videoStopDecoding === 'function') window.videoStopDecoding();
                localStorage.setItem('activeCipherTab', 'video');
            } else {
                tabImage.classList.add('active'); tabVideo.classList.remove('active');
                pageImage.classList.add('active-page'); pageVideo.classList.remove('active-page');
                if (typeof window.videoStopDecoding === 'function') window.videoStopDecoding(); // 停止视频播放
                localStorage.setItem('activeCipherTab', 'image');
            }
        }

        const saved = localStorage.getItem('activeCipherTab');
        if (saved === 'image') switchToTab('image'); else switchToTab('video');

        tabVideo.addEventListener('click', () => switchToTab('video'));
        tabImage.addEventListener('click', () => switchToTab('image'));
        refreshBtn.addEventListener('click', () => location.reload());
    })();

    // ==================== 视频解密失败说明弹窗 ====================
    (function() {
        const decryptFailBtn = document.getElementById('decryptFailBtn');
        const decryptFailModal = document.getElementById('decryptFailModal');
        const closeDecryptFailModalBtn = document.getElementById('closeDecryptFailModalBtn');
        const closeDecryptFailModalBtnBottom = document.getElementById('closeDecryptFailModalBtnBottom');

        // 显示弹窗
        decryptFailBtn.addEventListener('click', () => {
            decryptFailModal.style.display = 'flex';
        });

        // 关闭弹窗
        closeDecryptFailModalBtn.addEventListener('click', () => {
            decryptFailModal.style.display = 'none';
        });

        closeDecryptFailModalBtnBottom.addEventListener('click', () => {
            decryptFailModal.style.display = 'none';
        });

        // 点击弹窗外部关闭
        window.addEventListener('click', (e) => {
            if (e.target === decryptFailModal) {
                decryptFailModal.style.display = 'none';
            }
        });
    })();
