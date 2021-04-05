// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/// Helper for testing write!()
pub struct WriteWrapper<'a> {
    buffer: &'a mut [u8],
    offset: usize,
}

impl<'a> WriteWrapper<'a> {
    pub fn new(buffer: &'a mut [u8]) -> Self {
        WriteWrapper { buffer, offset: 0 }
    }
}

impl<'a> core::fmt::Write for WriteWrapper<'a> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let bytes = s.as_bytes();
        let bytes_left = &mut self.buffer[self.offset..];
        if bytes_left.len() < bytes.len() {
            return Err(core::fmt::Error);
        }
        let last_left = &mut bytes_left[..bytes.len()];
        last_left.copy_from_slice(bytes);
        self.offset += bytes.len();

        Ok(())
    }
}
